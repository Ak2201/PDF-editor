/*
 * Pagecraft TextEdit: true in-place text replacement inside PDF content streams.
 *
 *  analyze(doc, page)          decode + interpret the page content, returning every glyph
 *                              with its exact origin / advance (CTM, text matrix, widths).
 *  match(an, edit, T)          find the glyphs of a text run (edit given in viewport coords,
 *                              T = user space → viewport) and verify them against its string.
 *  rewrite(an, glyphs)         content stream with exactly those glyphs removed; every other
 *                              glyph keeps its position (removed glyphs become TJ kerning).
 *  setContent(doc, page, s)    write a rewritten stream back as the page's single content stream.
 *  layoutLine(an, m, s, first) encode new text with the ORIGINAL font (keeps original glyph
 *                              positions of unchanged prefix/suffix characters).
 *  drawOps(doc, an, m, lines)  pdf-lib operators that draw the new text with the original
 *                              font resource, size, spacing, scaling, rise, render mode, colour.
 */
(function () {
  'use strict';
  const L = PDFLib;
  const { PDFName, PDFDict, PDFArray, PDFNumber, PDFRawStream, PDFStream, PDFHexString, PDFOperator } = L;

  /* ---------------- matrices: [a b c d e f], p' = p × M; mul(A,B) = apply A then B ---------------- */
  const I = [1, 0, 0, 1, 0, 0];
  function mul(m1, m2) {
    return [
      m1[0] * m2[0] + m1[1] * m2[2], m1[0] * m2[1] + m1[1] * m2[3],
      m1[2] * m2[0] + m1[3] * m2[2], m1[2] * m2[1] + m1[3] * m2[3],
      m1[4] * m2[0] + m1[5] * m2[2] + m2[4], m1[4] * m2[1] + m1[5] * m2[3] + m2[5],
    ];
  }
  const apply = (m, x, y) => [m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5]];
  const inv = (m) => {
    const d = m[0] * m[3] - m[1] * m[2];
    return [m[3] / d, -m[1] / d, -m[2] / d, m[0] / d, (m[2] * m[5] - m[3] * m[4]) / d, (m[1] * m[4] - m[0] * m[5]) / d];
  };

  /* ---------------- bytes <-> latin1 ---------------- */
  function toLatin1(u8) {
    let s = '';
    for (let i = 0; i < u8.length; i += 0x8000) s += String.fromCharCode.apply(null, u8.subarray(i, i + 0x8000));
    return s;
  }
  function fromLatin1(s) {
    const u = new Uint8Array(s.length);
    for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i) & 255;
    return u;
  }
  const hexOf = (bytes) => { let h = ''; for (let i = 0; i < bytes.length; i++) h += bytes.charCodeAt(i).toString(16).padStart(2, '0'); return h; };
  function fmt(n) {
    if (!isFinite(n)) return '0';
    let s = (Math.round(n * 1e6) / 1e6).toFixed(6).replace(/\.?0+$/, '');
    if (s === '-0' || s === '') s = '0';
    return s;
  }

  /* ---------------- streams ---------------- */
  function streamBytes(doc, obj) {
    if (obj instanceof L.PDFRef) obj = doc.context.lookup(obj);
    if (!obj) return new Uint8Array(0);
    if (obj instanceof PDFRawStream) return L.decodePDFRawStream(obj).decode();
    if (typeof obj.getUnencodedContents === 'function') return obj.getUnencodedContents();
    if (typeof obj.getContents === 'function') return obj.getContents();
    throw new Error('Unsupported content stream');
  }
  function readContent(doc, page) {
    const c = page.node.get(PDFName.of('Contents'));
    const obj = c instanceof L.PDFRef ? doc.context.lookup(c) : c;
    if (!obj) return '';
    if (obj instanceof PDFArray) {
      const parts = [];
      for (let i = 0; i < obj.size(); i++) parts.push(toLatin1(streamBytes(doc, obj.get(i))));
      return parts.join('\n');
    }
    if (obj instanceof PDFStream) return toLatin1(streamBytes(doc, obj));
    return '';
  }

  /* ---------------- tokenizer / operator parser ---------------- */
  const WS = new Set([0, 9, 10, 12, 13, 32]);
  const DELIM = new Set('()<>[]{}/%'.split('').map((c) => c.charCodeAt(0)));
  const isWS = (c) => WS.has(c);
  const isReg = (c) => !WS.has(c) && !DELIM.has(c);

  function parseOps(s) {
    const ops = [];
    const n = s.length;
    let i = 0;
    let stack = []; // operand values
    let argStart = -1;
    const arrStack = [];
    const push = (v, start) => {
      if (arrStack.length) arrStack[arrStack.length - 1].push(v);
      else { if (!stack.length) argStart = start; stack.push(v); }
    };
    while (i < n) {
      const c = s.charCodeAt(i);
      if (isWS(c)) { i++; continue; }
      if (c === 37) { while (i < n && s[i] !== '\n' && s[i] !== '\r') i++; continue; } // %
      const start = i;
      if (c === 47) { // name
        i++;
        while (i < n && isReg(s.charCodeAt(i))) i++;
        const raw = s.slice(start + 1, i).replace(/#([0-9a-fA-F]{2})/g, (_, h) => String.fromCharCode(parseInt(h, 16)));
        push({ t: 'name', v: raw, s: start, e: i }, start);
        continue;
      }
      if (c === 40) { // literal string
        let depth = 1, out = '';
        i++;
        while (i < n && depth) {
          const ch = s[i];
          if (ch === '\\') {
            const nx = s[i + 1];
            i += 2;
            if (nx === 'n') out += '\n'; else if (nx === 'r') out += '\r'; else if (nx === 't') out += '\t';
            else if (nx === 'b') out += '\b'; else if (nx === 'f') out += '\f';
            else if (nx === '\r') { if (s[i] === '\n') i++; } else if (nx === '\n') { /* continuation */ }
            else if (nx >= '0' && nx <= '7') {
              let o = nx;
              while (o.length < 3 && s[i] >= '0' && s[i] <= '7') o += s[i++];
              out += String.fromCharCode(parseInt(o, 8) & 255);
            } else if (nx !== undefined) out += nx;
            continue;
          }
          if (ch === '(') depth++;
          else if (ch === ')') { depth--; if (!depth) { i++; break; } }
          if (ch === '\r') { out += '\n'; if (s[i + 1] === '\n') i++; i++; continue; }
          out += ch;
          i++;
        }
        push({ t: 'str', v: out, s: start, e: i }, start);
        continue;
      }
      if (c === 60) { // < hex or <<
        if (s[i + 1] === '<') { i += 2; push({ t: 'dictStart', s: start, e: i }, start); arrStack.push([]); arrStack[arrStack.length - 1].dict = true; continue; }
        const j = s.indexOf('>', i);
        const hx = s.slice(i + 1, j < 0 ? n : j).replace(/[^0-9a-fA-F]/g, '');
        const h2 = hx.length % 2 ? hx + '0' : hx;
        let out = '';
        for (let k = 0; k < h2.length; k += 2) out += String.fromCharCode(parseInt(h2.substr(k, 2), 16));
        i = j < 0 ? n : j + 1;
        push({ t: 'str', v: out, hex: true, s: start, e: i }, start);
        continue;
      }
      if (c === 62 && s[i + 1] === '>') { // >>
        i += 2;
        const d = arrStack.pop();
        // dictStart was pushed into the outer level; replace it with a dict value
        const holder = arrStack.length ? arrStack[arrStack.length - 1] : stack;
        const idx = holder.length - 1;
        if (idx >= 0 && holder[idx].t === 'dictStart') holder[idx] = { t: 'dict', v: d || [], s: holder[idx].s, e: i };
        continue;
      }
      if (c === 91) { i++; push({ t: 'arrStart', s: start }, start); arrStack.push([]); continue; }
      if (c === 93) {
        i++;
        const a = arrStack.pop() || [];
        const holder = arrStack.length ? arrStack[arrStack.length - 1] : stack;
        const idx = holder.length - 1;
        if (idx >= 0 && holder[idx].t === 'arrStart') holder[idx] = { t: 'arr', v: a, s: holder[idx].s, e: i };
        continue;
      }
      if (c === 123 || c === 125) { i++; continue; } // PostScript braces (Type4 functions) – ignore
      // regular token: number or operator/keyword
      while (i < n && isReg(s.charCodeAt(i))) i++;
      if (i === start) { i++; continue; }
      const tok = s.slice(start, i);
      if (/^[+-]?(\d+\.?\d*|\.\d+)$/.test(tok) || /^[+-]?\d*\.\d*$/.test(tok) && tok !== '.' ) {
        push({ t: 'num', v: parseFloat(tok) || 0, s: start, e: i }, start);
        continue;
      }
      if (tok === 'true' || tok === 'false' || tok === 'null') { push({ t: 'kw', v: tok, s: start, e: i }, start); continue; }
      if (arrStack.length) { arrStack[arrStack.length - 1].push({ t: 'kw', v: tok, s: start, e: i }); continue; }
      // operator
      const op = { op: tok, args: stack, s: stack.length ? argStart : start, e: i };
      stack = [];
      ops.push(op);
      if (tok === 'ID') {
        // inline image data: skip one whitespace then binary data up to whitespace + EI + delimiter
        let k = i + 1;
        let found = -1;
        while (k < n - 1) {
          if (s[k] === 'E' && s[k + 1] === 'I' && isWS(s.charCodeAt(k - 1)) && (k + 2 >= n || isWS(s.charCodeAt(k + 2)) || DELIM.has(s.charCodeAt(k + 2)))) { found = k; break; }
          k++;
        }
        const end = found < 0 ? n : found + 2;
        ops.push({ op: 'EI', args: [], s: found < 0 ? n : found, e: end });
        i = end;
      }
    }
    return ops;
  }

  /* ---------------- encodings & glyph names ---------------- */
  let tables = null;
  function getTables() {
    if (tables) return tables;
    const win = L.StandardFontEmbedder.for('Helvetica').encoding.unicodeMappings; // cp -> [code, name]
    const nameToUni = new Map();
    const winCodeToName = new Array(256).fill(null);
    for (const cp in win) {
      const [code, name] = win[cp];
      if (!nameToUni.has(name)) nameToUni.set(name, String.fromCodePoint(+cp));
      if (winCodeToName[code] == null) winCodeToName[code] = name;
    }
    Object.entries({ fi: 'fi', fl: 'fl', ff: 'ff', ffi: 'ffi', ffl: 'ffl', dotlessi: 'ı', Lslash: 'Ł', lslash: 'ł', fraction: '⁄', minus: '−', nbspace: ' ', sfthyphen: '­' })
      .forEach(([k, v]) => { if (!nameToUni.has(k)) nameToUni.set(k, v); });
    const stdCodeToName = winCodeToName.map((nm, c) => (c >= 32 && c <= 126 ? nm : null));
    stdCodeToName[39] = 'quoteright';
    stdCodeToName[96] = 'quoteleft';
    Object.assign(stdCodeToName, { 161: 'exclamdown', 162: 'cent', 163: 'sterling', 164: 'fraction', 165: 'yen', 166: 'florin', 167: 'section', 168: 'currency', 169: 'quotesingle', 170: 'quotedblleft', 171: 'guillemotleft', 172: 'guilsinglleft', 173: 'guilsinglright', 174: 'fi', 175: 'fl', 177: 'endash', 178: 'dagger', 179: 'daggerdbl', 180: 'periodcentered', 182: 'paragraph', 183: 'bullet', 184: 'quotesinglbase', 185: 'quotedblbase', 186: 'quotedblright', 187: 'guillemotright', 188: 'ellipsis', 189: 'perthousand', 191: 'questiondown', 193: 'grave', 194: 'acute', 195: 'circumflex', 196: 'tilde', 197: 'macron', 198: 'breve', 199: 'dotaccent', 200: 'dieresis', 202: 'ring', 203: 'cedilla', 205: 'hungarumlaut', 206: 'ogonek', 207: 'caron', 208: 'emdash', 225: 'AE', 227: 'ordfeminine', 232: 'Lslash', 233: 'Oslash', 234: 'OE', 235: 'ordmasculine', 241: 'ae', 245: 'dotlessi', 248: 'lslash', 249: 'oslash', 250: 'oe', 251: 'germandbls' });
    const macUpper = 'ÄÅÇÉÑÖÜáàâäãåçéèêëíìîïñóòôöõúùûü†°¢£§•¶ß®©™´¨≠ÆØ∞±≤≥¥µ∂∑∏π∫ªºΩæø¿¡¬√ƒ≈∆«»… ÀÃÕŒœ–—“”‘’÷◊ÿŸ⁄€‹›ﬁﬂ‡·‚„‰ÂÊÁËÈÍÎÏÌÓÔÒÚÛÙıˆ˜¯˘˙˚¸˝˛ˇ';
    const uniToName = new Map();
    nameToUni.forEach((u, nm) => { if (!uniToName.has(u)) uniToName.set(u, nm); });
    const macCodeToName = winCodeToName.map((nm, c) => (c >= 32 && c <= 126 ? nm : null));
    if (macUpper.length === 128) {
      for (let k = 0; k < 128; k++) {
        const u = macUpper[k];
        macCodeToName[128 + k] = uniToName.get(u) || 'uni' + u.charCodeAt(0).toString(16).toUpperCase().padStart(4, '0');
      }
    }
    const symbolic = (nm) => {
      const em = L.StandardFontEmbedder.for(nm).encoding.unicodeMappings;
      const arr = new Array(256).fill(null);
      for (const cp in em) { const [code, name] = em[cp]; arr[code] = name; if (!nameToUni.has(name)) nameToUni.set(name, String.fromCodePoint(+cp)); }
      return arr;
    };
    tables = {
      nameToUni, winCodeToName, stdCodeToName, macCodeToName,
      symbolCodeToName: symbolic('Symbol'), zapfCodeToName: symbolic('ZapfDingbats'),
    };
    return tables;
  }
  function glyphNameToUni(nm) {
    if (!nm) return null;
    const t = getTables();
    if (t.nameToUni.has(nm)) return t.nameToUni.get(nm);
    let m = /^uni([0-9A-Fa-f]{4,})$/.exec(nm);
    if (m) { let s = ''; for (let k = 0; k + 4 <= m[1].length; k += 4) s += String.fromCharCode(parseInt(m[1].substr(k, 4), 16)); return s; }
    m = /^u([0-9A-Fa-f]{4,6})$/.exec(nm);
    if (m) return String.fromCodePoint(parseInt(m[1], 16));
    if (nm.length === 1) return nm;
    const base = nm.split('.')[0];
    if (base !== nm) return glyphNameToUni(base);
    return null;
  }

  const STD14 = {
    'Helvetica': 'Helvetica', 'Helvetica-Bold': 'Helvetica-Bold', 'Helvetica-Oblique': 'Helvetica-Oblique', 'Helvetica-BoldOblique': 'Helvetica-BoldOblique',
    'Times-Roman': 'Times-Roman', 'Times-Bold': 'Times-Bold', 'Times-Italic': 'Times-Italic', 'Times-BoldItalic': 'Times-BoldItalic',
    'Courier': 'Courier', 'Courier-Bold': 'Courier-Bold', 'Courier-Oblique': 'Courier-Oblique', 'Courier-BoldOblique': 'Courier-BoldOblique',
    'Symbol': 'Symbol', 'ZapfDingbats': 'ZapfDingbats',
  };

  /* ---------------- ToUnicode CMap ---------------- */
  function hexToStr16(h) {
    let s = '';
    for (let k = 0; k + 4 <= h.length; k += 4) s += String.fromCharCode(parseInt(h.substr(k, 4), 16));
    if (h.length % 4 === 2) s += String.fromCharCode(parseInt(h.substr(h.length - 2), 16));
    return s;
  }
  function parseToUnicode(txt) {
    const map = new Map();
    let nbytes = 0;
    const cs = /begincodespacerange([\s\S]*?)endcodespacerange/g;
    let m;
    while ((m = cs.exec(txt))) { const h = /<([0-9a-fA-F]+)>/.exec(m[1]); if (h) nbytes = Math.max(nbytes, h[1].length / 2); }
    const bfc = /beginbfchar([\s\S]*?)endbfchar/g;
    while ((m = bfc.exec(txt))) {
      const re = /<([0-9a-fA-F]+)>\s*<([0-9a-fA-F]*)>/g;
      let p;
      while ((p = re.exec(m[1]))) map.set(parseInt(p[1], 16), hexToStr16(p[2]));
    }
    const bfr = /beginbfrange([\s\S]*?)endbfrange/g;
    while ((m = bfr.exec(txt))) {
      const re = /<([0-9a-fA-F]+)>\s*<([0-9a-fA-F]+)>\s*(<([0-9a-fA-F]*)>|\[([^\]]*)\])/g;
      let p;
      while ((p = re.exec(m[1]))) {
        const lo = parseInt(p[1], 16), hi = parseInt(p[2], 16);
        if (hi - lo > 65535) continue;
        if (p[4] != null) {
          const base = p[4];
          const prefix = base.slice(0, -4), last = parseInt(base.slice(-4) || '0', 16);
          for (let c = lo; c <= hi; c++) map.set(c, hexToStr16(prefix) + String.fromCharCode(last + (c - lo)));
        } else {
          const items = (p[5].match(/<([0-9a-fA-F]*)>/g) || []).map((x) => hexToStr16(x.slice(1, -1)));
          for (let c = lo; c <= hi && c - lo < items.length; c++) map.set(c, items[c - lo]);
        }
      }
    }
    return { map, nbytes };
  }

  /* ---------------- fonts ---------------- */
  function num(doc, o, d) {
    if (o instanceof L.PDFRef) o = doc.context.lookup(o);
    return o instanceof PDFNumber ? o.asNumber() : d;
  }
  function nameOf(doc, o) {
    if (o instanceof L.PDFRef) o = doc.context.lookup(o);
    return o instanceof PDFName ? o.decodeText ? o.decodeText() : o.asString().slice(1) : null;
  }
  function look(doc, d, key) {
    if (!d) return undefined;
    const v = d.get(PDFName.of(key));
    return v instanceof L.PDFRef ? doc.context.lookup(v) : v;
  }

  function loadFont(doc, key, fdict) {
    const f = { key, kind: 'unknown', nb: 1, widths: null, toUni: null, reverse: null, subset: false, base: '', used: new Set(), std: null };
    if (!(fdict instanceof PDFDict)) return f;
    const sub = nameOf(doc, look(doc, fdict, 'Subtype'));
    const base = nameOf(doc, look(doc, fdict, 'BaseFont')) || '';
    f.base = base;
    f.subset = /^[A-Z]{6}\+/.test(base);
    const bare = base.replace(/^[A-Z]{6}\+/, '');
    const tu = look(doc, fdict, 'ToUnicode');
    if (tu instanceof PDFStream) {
      try { f.toUni = parseToUnicode(toLatin1(streamBytes(doc, tu))).map; } catch (err) { f.toUni = null; }
    }
    if (sub === 'Type0') {
      const enc = nameOf(doc, look(doc, fdict, 'Encoding'));
      const desc = look(doc, fdict, 'DescendantFonts');
      const cid = desc instanceof PDFArray ? (desc.get(0) instanceof L.PDFRef ? doc.context.lookup(desc.get(0)) : desc.get(0)) : null;
      if (enc !== 'Identity-H' || !(cid instanceof PDFDict)) { f.kind = 'unsupported'; f.reason = 'font encoding ' + (enc || 'embedded CMap'); return f; }
      f.kind = 'type0';
      f.nb = 2;
      const dw = num(doc, look(doc, cid, 'DW'), 1000);
      const wmap = new Map();
      const W = look(doc, cid, 'W');
      if (W instanceof PDFArray) {
        const arr = W.asArray().map((x) => (x instanceof L.PDFRef ? doc.context.lookup(x) : x));
        for (let k = 0; k < arr.length;) {
          const c0 = num(doc, arr[k], null);
          const nx = arr[k + 1];
          if (nx instanceof PDFArray) {
            nx.asArray().forEach((w, j) => wmap.set(c0 + j, num(doc, w, dw)));
            k += 2;
          } else {
            const c1 = num(doc, nx, c0), w = num(doc, arr[k + 2], dw);
            for (let c = c0; c <= c1 && c - c0 < 65536; c++) wmap.set(c, w);
            k += 3;
          }
        }
      }
      f.width = (code) => (wmap.has(code) ? wmap.get(code) : dw);
      f.hasWidth = (code) => wmap.has(code) || dw > 0;
      f.uni = (code) => (f.toUni && f.toUni.has(code) ? f.toUni.get(code) : null);
      return f;
    }
    if (sub === 'Type3') {
      f.kind = 'type3';
      const fm = look(doc, fdict, 'FontMatrix');
      const a = fm instanceof PDFArray ? num(doc, fm.get(0), 0.001) : 0.001;
      const first = num(doc, look(doc, fdict, 'FirstChar'), 0);
      const Wd = look(doc, fdict, 'Widths');
      const ws = Wd instanceof PDFArray ? Wd.asArray().map((x) => num(doc, x, 0)) : [];
      f.width = (code) => (code - first >= 0 && code - first < ws.length ? ws[code - first] * a * 1000 : 0);
      f.uni = (code) => (f.toUni && f.toUni.has(code) ? f.toUni.get(code) : null);
      return f;
    }
    // simple font (Type1, MMType1, TrueType)
    f.kind = 'simple';
    const t = getTables();
    f.std = STD14[bare] || null;
    const enc = look(doc, fdict, 'Encoding');
    let baseNames = null;
    const diffs = new Map();
    const encName = enc instanceof PDFName ? nameOf(doc, enc) : enc instanceof PDFDict ? nameOf(doc, look(doc, enc, 'BaseEncoding')) : null;
    if (encName === 'WinAnsiEncoding') baseNames = t.winCodeToName;
    else if (encName === 'MacRomanEncoding') baseNames = t.macCodeToName;
    else if (encName === 'StandardEncoding') baseNames = t.stdCodeToName;
    else if (f.std === 'Symbol') baseNames = t.symbolCodeToName;
    else if (f.std === 'ZapfDingbats') baseNames = t.zapfCodeToName;
    else if (f.std || sub === 'Type1') baseNames = t.stdCodeToName;
    else baseNames = t.winCodeToName; // TrueType without encoding: assume WinAnsi-like for ASCII
    if (enc instanceof PDFDict) {
      const D = look(doc, enc, 'Differences');
      if (D instanceof PDFArray) {
        let code = 0;
        D.asArray().forEach((x) => {
          if (x instanceof L.PDFRef) x = doc.context.lookup(x);
          if (x instanceof PDFNumber) code = x.asNumber();
          else if (x instanceof PDFName) { diffs.set(code, nameOf(doc, x)); code++; }
        });
      }
    }
    f.glyphName = (code) => (diffs.has(code) ? diffs.get(code) : baseNames[code] || null);
    f.uni = (code) => {
      if (f.toUni && f.toUni.has(code)) return f.toUni.get(code);
      return glyphNameToUni(f.glyphName(code));
    };
    const Wd = look(doc, fdict, 'Widths');
    const fd = look(doc, fdict, 'FontDescriptor');
    const missing = num(doc, look(doc, fd, 'MissingWidth'), 0);
    if (Wd instanceof PDFArray) {
      const first = num(doc, look(doc, fdict, 'FirstChar'), 0);
      const ws = Wd.asArray().map((x) => num(doc, x, 0));
      f.width = (code) => (code - first >= 0 && code - first < ws.length ? ws[code - first] : missing);
      f.hasWidth = (code) => code - first >= 0 && code - first < ws.length && ws[code - first] > 0;
    } else if (f.std) {
      const em = L.StandardFontEmbedder.for(f.std);
      f.width = (code) => {
        const nm = f.glyphName(code);
        if (!nm) return null;
        try { const w = em.font.getWidthOfGlyph(nm); return w == null ? null : w; } catch (err) { return null; }
      };
      f.hasWidth = (code) => f.width(code) != null;
    } else {
      f.width = () => null; // unknown metrics – positions can't be trusted
      f.hasWidth = () => false;
    }
    return f;
  }

  /* ---------------- interpreter ---------------- */
  function cloneGS(g) {
    return Object.assign({}, g, { ctm: g.ctm.slice(), fill: g.fill.slice(), stroke: g.stroke.slice(), extg: g.extg.slice() });
  }

  function analyze(doc, page) {
    if (doc.isEncrypted) return { ok: false, reason: 'encrypted document', glyphs: [] };
    const content = readContent(doc, page);
    const ops = parseOps(content);
    const res = page.node.Resources();
    const fontRes = res ? look(doc, res, 'Font') : null;
    const fonts = new Map();
    const fontOf = (key) => {
      if (!fonts.has(key)) {
        let fd = null;
        if (fontRes instanceof PDFDict) fd = look(doc, fontRes, key);
        fonts.set(key, loadFont(doc, key, fd));
      }
      return fonts.get(key);
    };
    const glyphs = [];
    let gs = { ctm: I.slice(), Tc: 0, Tw: 0, Th: 1, TL: 0, font: null, fs: 0, Tr: 0, Ts: 0, fill: [['g', [{ t: 'num', v: 0 }]]], stroke: [['G', [{ t: 'num', v: 0 }]]], extg: [], lw: null };
    const stack = [];
    let Tm = I.slice(), Tlm = I.slice(), unreliable = false;
    const nums = (args) => args.map((a) => (a && a.t === 'num' ? a.v : 0));
    const td = (tx, ty) => { Tlm = mul([1, 0, 0, 1, tx, ty], Tlm); Tm = Tlm.slice(); unreliable = false; };

    function show(oi, elems) {
      const f = gs.font ? fontOf(gs.font) : null;
      const snap = { font: gs.font, fs: gs.fs, Tc: gs.Tc, Tw: gs.Tw, Th: gs.Th, Ts: gs.Ts, Tr: gs.Tr, ctm: gs.ctm.slice(), fill: gs.fill.slice(), stroke: gs.stroke.slice(), extg: gs.extg.slice(), lw: gs.lw };
      const fs = gs.fs, Th = gs.Th;
      elems.forEach((el, ei) => {
        if (el.t === 'num') { Tm = mul([1, 0, 0, 1, -el.v / 1000 * fs * Th, 0], Tm); return; }
        if (el.t !== 'str') return;
        if (!f || f.kind === 'unknown' || f.kind === 'unsupported') { unreliable = true; return; }
        const b = el.v;
        for (let bi = 0; bi + f.nb <= b.length; bi += f.nb) {
          const code = f.nb === 2 ? (b.charCodeAt(bi) << 8) | b.charCodeAt(bi + 1) : b.charCodeAt(bi);
          let w0 = f.width(code);
          let ok = !unreliable && fs !== 0;
          if (w0 == null) { w0 = 0; unreliable = true; ok = false; }
          const isSpace = f.nb === 1 && code === 32;
          const tx = (w0 / 1000 * fs + gs.Tc + (isSpace ? gs.Tw : 0)) * Th;
          f.used.add(code);
          glyphs.push({
            op: oi, el: ei, bi, nb: f.nb, code, w0, tx, isSpace, uni: f.uni(code), Tm: Tm.slice(), st: snap,
            ok: ok && f.kind !== 'type3', fkind: f.kind,
          });
          Tm = mul([1, 0, 0, 1, tx, 0], Tm);
        }
      });
      Object.assign(ops[oi], { tlm: Tlm.slice(), tmAfter: Tm.slice(), st: snap });
    }

    ops.forEach((o, oi) => {
      const a = o.args;
      switch (o.op) {
        case 'q': stack.push(cloneGS(gs)); break;
        case 'Q': if (stack.length) gs = stack.pop(); break;
        case 'cm': { const m = nums(a); if (m.length === 6) gs.ctm = mul(m, gs.ctm); break; }
        case 'BT': Tm = I.slice(); Tlm = I.slice(); unreliable = false; break;
        case 'Tf': if (a[0] && a[0].t === 'name') gs.font = a[0].v; gs.fs = a[1] && a[1].t === 'num' ? a[1].v : 0; break;
        case 'Tc': gs.Tc = nums(a)[0] || 0; break;
        case 'Tw': gs.Tw = nums(a)[0] || 0; break;
        case 'Tz': gs.Th = (a[0] && a[0].t === 'num' ? a[0].v : 100) / 100; break;
        case 'TL': gs.TL = nums(a)[0] || 0; break;
        case 'Ts': gs.Ts = nums(a)[0] || 0; break;
        case 'Tr': gs.Tr = nums(a)[0] || 0; break;
        case 'Td': { const v = nums(a); td(v[0] || 0, v[1] || 0); break; }
        case 'TD': { const v = nums(a); gs.TL = -(v[1] || 0); td(v[0] || 0, v[1] || 0); break; }
        case 'Tm': { const m = nums(a); if (m.length === 6) { Tlm = m; Tm = m.slice(); unreliable = false; } break; }
        case 'T*': td(0, -gs.TL); break;
        case 'Tj': show(oi, a.length ? [a[a.length - 1]] : []); break;
        case 'TJ': show(oi, a.length && a[a.length - 1].t === 'arr' ? a[a.length - 1].v : []); break;
        case "'": td(0, -gs.TL); show(oi, a.length ? [a[a.length - 1]] : []); break;
        case '"': { const v = nums(a); gs.Tw = v[0] || 0; gs.Tc = v[1] || 0; td(0, -gs.TL); show(oi, a.length ? [a[a.length - 1]] : []); break; }
        case 'g': case 'rg': case 'k': gs.fill = [[o.op, a]]; break;
        case 'cs': gs.fill = [['cs', a]]; break;
        case 'sc': case 'scn': gs.fill = gs.fill.filter((x) => x[0] === 'cs').concat([[o.op, a]]); break;
        case 'G': case 'RG': case 'K': gs.stroke = [[o.op, a]]; break;
        case 'CS': gs.stroke = [['CS', a]]; break;
        case 'SC': case 'SCN': gs.stroke = gs.stroke.filter((x) => x[0] === 'CS').concat([[o.op, a]]); break;
        case 'gs': gs.extg.push(a); break;
        case 'w': gs.lw = nums(a)[0]; break;
        default: break;
      }
    });
    const byOp = new Map();
    glyphs.forEach((g, gi) => { g.gi = gi; if (!byOp.has(g.op)) byOp.set(g.op, []); byOp.get(g.op).push(g); });
    return { ok: true, content, ops, glyphs, byOp, fonts };
  }

  /* ---------------- matching ---------------- */
  const norm = (s) => (s || '').normalize('NFKC').replace(/\s+/g, '');
  function glyphGeom(g, T) {
    const m = mul(mul([g.st.fs * g.st.Th, 0, 0, g.st.fs, 0, g.st.Ts], mul(g.Tm, g.st.ctm)), T);
    const unit = mul(mul(g.Tm, g.st.ctm), T); // text space -> viewport
    const ux = Math.hypot(unit[0], unit[1]);
    return { x: m[4], y: m[5], size: Math.abs(m[3]), a: m[0], b: m[1], c: m[2], adv: g.tx * ux };
  }

  /**
   * edit = { x0, x1, baseline, fs, str } in viewport coords (pdf.js viewport scale 1).
   * Returns { ok, reason, glyphs, ... } — glyphs sorted left→right.
   */
  function match(an, edit, T) {
    if (!an || !an.ok) return { ok: false, reason: (an && an.reason) || 'no analysis' };
    const fs = edit.fs;
    const hits = [];
    for (const g of an.glyphs) {
      const q = glyphGeom(g, T);
      if (!(q.a > 0) || Math.abs(q.b) > 1e-3 * q.a || Math.abs(q.c) > 1e-3 * q.a) continue;
      if (Math.abs(q.y - edit.baseline) > fs * 0.3) continue;
      if (Math.abs(q.size - fs) > Math.max(0.3, fs * 0.08)) continue;
      const cx = q.x + Math.max(0, q.adv) / 2;
      if (cx < edit.x0 - 0.01 || cx > edit.x1 + 0.01) continue;
      hits.push({ g, q });
    }
    if (!hits.length) return { ok: false, reason: 'text not found in page content (it may be inside a form XObject)' };
    hits.sort((p, r) => p.q.x - r.q.x);
    const gl = hits.map((h) => h.g);
    if (gl.some((g) => !g.ok)) return { ok: false, reason: gl.some((g) => g.fkind === 'type3') ? 'Type3 font' : 'unknown glyph widths' };
    if (gl.some((g) => g.st.Tr === 3 || g.st.Tr >= 4)) return { ok: false, reason: 'invisible or clipping text' };
    // verify against the extracted string
    const got = gl.map((g) => (g.uni == null ? '�' : g.uni)).join('');
    const a = norm(got), b = norm(edit.str);
    let same = a.length === b.length;
    for (let k = 0; same && k < a.length; k++) if (a[k] !== b[k] && a[k] !== '�') same = false;
    if (!same) return { ok: false, reason: `glyph text mismatch ("${got}" vs "${edit.str}")` };
    const g0 = gl[0], st = g0.st;
    if (gl.some((g) => g.st.font !== st.font || Math.abs(g.st.fs - st.fs) > 1e-6)) {
      return { ok: true, glyphs: gl, native: false, reason: 'mixed fonts in run' };
    }
    // offsets along the baseline, in unscaled text-space units of glyph 0
    const M0 = mul(g0.Tm, st.ctm);
    const o0 = apply(M0, 0, 0);
    const uu = M0[0] * M0[0] + M0[1] * M0[1];
    const tokens = [];
    let prev = null;
    gl.forEach((g) => {
      const o = apply(mul(g.Tm, g.st.ctm), 0, 0);
      const off = ((o[0] - o0[0]) * M0[0] + (o[1] - o0[1]) * M0[1]) / uu;
      if (prev) {
        const end = prev.off + prev.g.tx;
        if (off - end > st.fs * 0.15 && !/\s/.test(prev.g.uni || '') && !/\s/.test(g.uni || '')) tokens.push({ t: 'vs', start: end, end: off });
      }
      const tk = { t: 'g', g, off, uni: g.uni };
      tokens.push(tk);
      prev = tk;
    });
    const unitVp = Math.hypot(mul(M0, T)[0], mul(M0, T)[1]);
    const originVp = apply(T, ...apply(mul([1, 0, 0, 1, 0, st.Ts], M0), 0, 0));
    return {
      ok: true, native: true, glyphs: gl, tokens, font: st.font, fs: st.fs, Tc: st.Tc, Tw: st.Tw, Th: st.Th, Ts: st.Ts, Tr: st.Tr,
      Tm0: g0.Tm, ctm: st.ctm, fill: st.fill, stroke: st.stroke, extg: st.extg, lw: st.lw, unitVp, originVp,
      color: colorHex(st.fill),
    };
  }

  function colorHex(fill) {
    try {
      const last = fill[fill.length - 1];
      const v = (last[1] || []).filter((x) => x.t === 'num').map((x) => x.v);
      const cs = fill.find((x) => x[0] === 'cs');
      const csn = cs && cs[1][0] ? cs[1][0].v : null;
      let rgb = null;
      if (last[0] === 'g' || ((last[0] === 'sc' || last[0] === 'scn') && csn === 'DeviceGray' && v.length === 1)) rgb = [v[0], v[0], v[0]];
      else if (last[0] === 'rg' || ((last[0] === 'sc' || last[0] === 'scn') && v.length === 3 && csn !== 'DeviceCMYK')) rgb = v;
      else if (last[0] === 'k' || ((last[0] === 'sc' || last[0] === 'scn') && v.length === 4)) rgb = [(1 - v[0]) * (1 - v[3]), (1 - v[1]) * (1 - v[3]), (1 - v[2]) * (1 - v[3])];
      if (!rgb) return null;
      return '#' + rgb.map((x) => Math.round(Math.max(0, Math.min(1, x)) * 255).toString(16).padStart(2, '0')).join('');
    } catch (err) { return null; }
  }

  /* ---------------- removal ---------------- */
  function rewrite(an, removeList, inserts) {
    const remove = new Set(removeList.map((g) => g.gi));
    const affected = new Set(removeList.map((g) => g.op));
    const edits = [];
    (inserts || []).forEach((ins) => { const o = an.ops[ins.op]; edits.push({ s: o.e, e: o.e, txt: '\n' + ins.text + '\n', after: true }); });
    affected.forEach((oi) => {
      const o = an.ops[oi];
      const gl = an.byOp.get(oi) || [];
      const elems = o.op === 'TJ' ? o.args[o.args.length - 1].v : [o.args[o.args.length - 1]];
      const out = [];
      const pushNum = (v) => {
        if (Math.abs(v) < 1e-9) return;
        if (out.length && out[out.length - 1].n != null) out[out.length - 1].n += v;
        else out.push({ n: v });
      };
      const pushBytes = (b) => {
        if (out.length && out[out.length - 1].b != null) out[out.length - 1].b += b;
        else out.push({ b });
      };
      elems.forEach((el, ei) => {
        if (el.t === 'num') { pushNum(el.v); return; }
        if (el.t !== 'str') return;
        const mine = gl.filter((g) => g.el === ei);
        mine.forEach((g) => {
          const bytes = el.v.substr(g.bi, g.nb);
          if (remove.has(g.gi)) pushNum(-(g.w0 + (g.st.Tc + (g.isSpace ? g.st.Tw : 0)) * 1000 / g.st.fs));
          else pushBytes(bytes);
        });
      });
      const arr = '[' + out.map((x) => (x.n != null ? fmt(x.n) : '<' + hexOf(x.b) + '>')).join(' ') + '] TJ';
      let txt;
      const raw = (t) => an.content.slice(t.s, t.e);
      if (o.op === "'") txt = 'T* ' + arr;
      else if (o.op === '"') txt = raw(o.args[0]) + ' Tw ' + raw(o.args[1]) + ' Tc T* ' + arr;
      else txt = arr;
      edits.push({ s: o.s, e: o.e, txt });
    });
    edits.sort((x, y) => x.s - y.s || (x.after ? 1 : 0) - (y.after ? 1 : 0));
    let res = '', pos = 0;
    edits.forEach((ed) => { res += an.content.slice(pos, ed.s) + ed.txt; pos = ed.e; });
    res += an.content.slice(pos);
    return 'q\n' + res + '\nQ\n';
  }

  function setContent(doc, page, latin1) {
    const stream = doc.context.flateStream(fromLatin1(latin1));
    page.node.set(PDFName.of('Contents'), doc.context.register(stream));
  }

  /* ---------------- re-encoding with the original font ---------------- */
  function reverseMap(f) {
    if (f.reverse) return f.reverse;
    const r = new Map();
    const add = (code, s) => {
      if (s == null || s === '') return;
      if (!r.has(s)) r.set(s, code);
    };
    if (f.toUni) f.toUni.forEach((s, code) => { if (f.kind !== 'simple' || code < 256) add(code, s); });
    if (f.kind === 'simple') for (let c = 0; c < 256; c++) add(c, f.uni(c));
    f.reverse = r;
    return r;
  }
  /** code for one character with the original font, or null if the glyph may be missing. */
  function encodeChar(f, ch) {
    if (!f || (f.kind !== 'simple' && f.kind !== 'type0')) return null;
    const code = reverseMap(f).get(ch);
    if (code == null) return null;
    const inToUni = f.toUni && f.toUni.has(code);
    if (f.kind === 'type0') {
      if (!inToUni) return null; // can't tell whether the subset holds this glyph
      return code;
    }
    if (f.subset && !inToUni && !f.used.has(code)) return null; // subset: only glyphs we know are present
    if (!f.hasWidth(code) && code !== 32) return null;
    return code;
  }

  function charsOf(s) { return Array.from(s); }

  /** Common prefix/suffix between the original glyph tokens and the new string. */
  function diffTokens(tokens, s) {
    const tokText = (t) => (t.t === 'vs' ? ' ' : t.uni);
    let pi = 0, sp = 0;
    while (pi < tokens.length) {
      const tt = tokText(tokens[pi]);
      if (tt == null || tt === '' || !s.startsWith(tt, sp)) break;
      sp += tt.length;
      pi++;
    }
    let si = tokens.length, ep = s.length;
    while (si > pi) {
      const tt = tokText(tokens[si - 1]);
      if (tt == null || tt === '' || ep - tt.length < sp || s.slice(ep - tt.length, ep) !== tt) break;
      ep -= tt.length;
      si--;
    }
    return { pi, sp, si, ep };
  }

  function sameState(a, b) {
    return a.font === b.font && a.fs === b.fs && a.Tc === b.Tc && a.Tw === b.Tw && a.Th === b.Th && a.Ts === b.Ts && a.Tr === b.Tr && a.lw === b.lw
      && JSON.stringify([a.fill, a.stroke, a.extg, a.ctm]) === JSON.stringify([b.fill, b.stroke, b.extg, b.ctm]);
  }

  /**
   * Minimal in-place edit of a single unmoved line: only the glyphs that actually change are
   * removed and drawn (with the state of the neighbouring original glyph); the suffix is only
   * touched when the new middle has a different width. Returns
   * { remove, items, m2 } | { missing } | null (not applicable → use full replacement).
   */
  function minimalEdit(an, m, s) {
    const f = an.fonts.get(m.font);
    if (!f) return null;
    const tokens = m.tokens;
    const { pi, sp, si, ep } = diffTokens(tokens, s);
    const pre = tokens.slice(0, pi), mid = tokens.slice(pi, si), suf = tokens.slice(si);
    const gOf = (arr) => arr.filter((t) => t.t === 'g');
    if (!mid.length && sp === ep) return { remove: [], items: [], m2: null };
    const ref = gOf(mid)[0] || gOf(pre).slice(-1)[0] || gOf(suf)[0];
    if (!ref) return null;
    const rs = ref.g.st;
    if (rs.font !== m.font) return null;
    const M0 = mul(m.Tm0, m.ctm), Mr = mul(ref.g.Tm, rs.ctm);
    for (let k = 0; k < 4; k++) if (Math.abs(M0[k] - Mr[k]) > 1e-9) return null;
    const tokStart = (t) => (t.t === 'vs' ? t.start : t.off);
    const tokEnd = (t) => (t.t === 'vs' ? t.end : t.off + t.g.tx);
    let start;
    if (mid.length) start = tokStart(mid[0]);
    else if (pre.length) start = tokEnd(pre[pre.length - 1]);
    else start = suf.length ? tokStart(suf[0]) : 0;
    const oldEnd = suf.length ? tokStart(suf[0]) : null;
    const fs = rs.fs, Th = rs.Th;
    const adv = (code, w0) => (w0 / 1000 * fs + rs.Tc + (f.nb === 1 && code === 32 ? rs.Tw : 0)) * Th;
    const items = [], missing = [];
    let cur = ref.off;
    const moveTo = (target) => {
      const d = target - cur;
      if (Math.abs(d) > 1e-7) items.push({ num: -d * 1000 / (fs * Th) });
      cur = target;
    };
    const emit = (code, w0) => {
      items.push({ bytes: f.nb === 2 ? String.fromCharCode(code >> 8, code & 255) : String.fromCharCode(code) });
      cur += adv(code, w0);
    };
    const gaps = tokens.filter((t) => t.t === 'vs').map((t) => t.end - t.start);
    let spaceGap = gaps.length ? gaps.reduce((x, y) => x + y, 0) / gaps.length : 0;
    if (!spaceGap) {
      const sc = encodeChar(f, ' ');
      spaceGap = sc != null ? adv(sc, f.width(sc) || 0) : 0.278 * fs * Th;
    }
    moveTo(start);
    for (const ch of Array.from(s.slice(sp, ep))) {
      const code = encodeChar(f, ch);
      if (code != null) emit(code, f.width(code) || 0);
      else if (/\s/.test(ch)) moveTo(cur + spaceGap);
      else missing.push(ch);
    }
    if (missing.length) return { missing };
    const remove = gOf(mid).map((t) => t.g);
    if (suf.length && Math.abs(cur - oldEnd) > 1e-6) {
      // the suffix has to move: redraw it shifted (only if it shares the reference state)
      if (gOf(suf).some((t) => !sameState(t.g.st, rs))) return null;
      const shift = cur - oldEnd;
      gOf(suf).forEach((t) => { moveTo(t.off + shift); emit(t.g.code, t.g.w0); remove.push(t.g); });
    }
    const m2 = { font: rs.font, fs: rs.fs, Tc: rs.Tc, Tw: rs.Tw, Th: rs.Th, Ts: rs.Ts, Tr: rs.Tr, Tm0: ref.g.Tm, ctm: rs.ctm, fill: rs.fill, stroke: rs.stroke, extg: rs.extg, lw: rs.lw };
    return { remove, items, m2 };
  }

  /**
   * Lay out one line of new text with the original font. For the first line the unchanged
   * prefix/suffix (vs. the original glyph tokens) keep their exact original positions.
   * Returns { items:[{bytes}|{num}], width (text units), missing:[] }.
   */
  function layoutLine(an, m, s, first) {
    const f = an.fonts.get(m.font);
    const fs = m.fs, Th = m.Th;
    const items = [];
    const missing = [];
    let pen = 0;
    const adv = (code, w0) => (w0 / 1000 * fs + m.Tc + (f.nb === 1 && code === 32 ? m.Tw : 0)) * Th;
    const moveTo = (target) => {
      const d = target - pen;
      if (Math.abs(d) > 1e-7) items.push({ num: -d * 1000 / (fs * Th) });
      pen = target;
    };
    const emit = (code, w0) => {
      const b = f.nb === 2 ? String.fromCharCode(code >> 8, code & 255) : String.fromCharCode(code);
      items.push({ bytes: b });
      pen += adv(code, w0);
    };
    const tokens = first ? m.tokens : [];
    const { pi, sp, si, ep } = diffTokens(tokens, s);
    for (let k = 0; k < pi; k++) {
      const t = tokens[k];
      if (t.t === 'vs') continue;
      moveTo(t.off);
      emit(t.g.code, t.g.w0);
    }
    if (pi > 0 && tokens[pi - 1].t === 'vs') moveTo(tokens[pi - 1].end);
    // middle
    const gaps = m.tokens.filter((t) => t.t === 'vs').map((t) => t.end - t.start);
    let spaceGap = gaps.length ? gaps.reduce((x, y) => x + y, 0) / gaps.length : 0;
    if (!spaceGap) {
      const sc = encodeChar(f, ' ');
      spaceGap = sc != null ? adv(sc, f.width(sc) || 0) : 0.278 * fs * Th;
    }
    for (const ch of charsOf(s.slice(sp, ep))) {
      const code = encodeChar(f, ch);
      if (code != null) { emit(code, f.width(code) || 0); continue; }
      if (/\s/.test(ch)) { pen += spaceGap; continue; }
      missing.push(ch);
    }
    // suffix
    if (si < tokens.length) {
      const t0 = tokens[si];
      const shift = pen - (t0.t === 'vs' ? t0.start : t0.off);
      for (let k = si; k < tokens.length; k++) {
        const t = tokens[k];
        if (t.t === 'vs') continue;
        moveTo(t.off + shift);
        emit(t.g.code, t.g.w0);
      }
    }
    return { items, width: pen, missing };
  }

  /* ---------------- inline (in-stream) drawing ---------------- */
  /** Merge adjacent strings / numbers of a TJ item list. */
  function compact(items) {
    const out = [];
    items.forEach((x) => {
      const last = out[out.length - 1];
      if (x.bytes != null && last && last.bytes != null) last.bytes += x.bytes;
      else if (x.num != null && last && last.num != null) last.num += x.num;
      else out.push(Object.assign({}, x));
    });
    return out.filter((x) => x.bytes != null || Math.abs(x.num) > 1e-9);
  }
  const pdfName = (n) => '/' + n.replace(/[^!-~]|[#()<>[\]{}\/%]/g, (c) => '#' + c.charCodeAt(0).toString(16).padStart(2, '0'));
  const argTxt = (a) => (a.t === 'num' ? fmt(a.v) : a.t === 'name' ? pdfName(a.v) : '');
  const opsTxt = (list) => list.map(([n, a]) => a.map(argTxt).join(' ') + (a.length ? ' ' : '') + n).join(' ');
  const mtx = (m) => m.map(fmtExact).join(' ');
  function fmtExact(v) { if (Number.isInteger(v)) return String(v); const t = String(+v.toPrecision(15)); return /e/.test(t) ? fmt(v) : t; }

  /** Text matrix that draws at the run origin moved by du (user space). */
  function lineTm(m, du) {
    if (!du || (Math.abs(du[0]) < 1e-12 && Math.abs(du[1]) < 1e-12)) return m.Tm0.slice();
    return mul(mul(mul(m.Tm0, m.ctm), [1, 0, 0, 1, du[0], du[1]]), inv(m.ctm));
  }

  /**
   * Content-stream text that draws `lines` inside the original text object, directly after
   * op `anchor` (same CTM, clip, marked content and reading order), then restores the text
   * state, colour and text/line matrices so everything after it renders exactly as before.
   * ds = draw state (font, fs, Tc, Tw, Th, Ts, Tr, fill); lines = [{ items, tm }].
   * Returns null when the state can't be restored exactly.
   */
  function inlineOps(an, anchor, ds, lines, opts = {}) {
    const o = an.ops[anchor];
    const cur = o && o.st;
    if (!cur || !o.tlm || !o.tmAfter || !cur.font || !cur.fs) return null;
    const out = [], back = [];
    if (ds.font !== cur.font || ds.fs !== cur.fs) { out.push(`${pdfName(ds.font)} ${fmtExact(ds.fs)} Tf`); back.push(`${pdfName(cur.font)} ${fmtExact(cur.fs)} Tf`); }
    if (ds.Tc !== cur.Tc) { out.push(`${fmtExact(ds.Tc)} Tc`); back.push(`${fmtExact(cur.Tc)} Tc`); }
    if (ds.Tw !== cur.Tw) { out.push(`${fmtExact(ds.Tw)} Tw`); back.push(`${fmtExact(cur.Tw)} Tw`); }
    if (ds.Th !== cur.Th) { out.push(`${fmtExact(ds.Th * 100)} Tz`); back.push(`${fmtExact(cur.Th * 100)} Tz`); }
    if (ds.Ts !== cur.Ts) { out.push(`${fmtExact(ds.Ts)} Ts`); back.push(`${fmtExact(cur.Ts)} Ts`); }
    if (ds.Tr !== cur.Tr) { out.push(`${fmtExact(ds.Tr)} Tr`); back.push(`${fmtExact(cur.Tr)} Tr`); }
    if (opts.rgb) { out.push(opts.rgb.map(fmt).join(' ') + ' rg'); back.push(opsTxt(cur.fill)); }
    else if (JSON.stringify(ds.fill) !== JSON.stringify(cur.fill)) { out.push(opsTxt(ds.fill)); back.push(opsTxt(cur.fill)); }
    let drew = false;
    lines.forEach((ln) => {
      if (!ln.items.some((x) => x.bytes != null)) return;
      drew = true;
      out.push(mtx(ln.tm) + ' Tm');
      out.push('[' + compact(ln.items).map((x) => (x.bytes != null ? '<' + hexOf(x.bytes) + '>' : fmt(x.num))).join(' ') + '] TJ');
    });
    if (!drew) return '';
    // restore: line matrix, then advance the text matrix to where the anchor op left it
    const L0 = o.tlm, A = o.tmAfter;
    let dx = 0;
    if (Math.abs(L0[0]) >= Math.abs(L0[1]) && Math.abs(L0[0]) > 1e-12) dx = (A[4] - L0[4]) / L0[0];
    else if (Math.abs(L0[1]) > 1e-12) dx = (A[5] - L0[5]) / L0[1];
    else return null;
    const chk = mul([1, 0, 0, 1, dx, 0], L0);
    if (Math.abs(chk[4] - A[4]) > 1e-6 || Math.abs(chk[5] - A[5]) > 1e-6) return null;
    out.push(...back);
    out.push(mtx(L0) + ' Tm');
    if (Math.abs(dx) > 1e-12) out.push(`[${fmtExact(-dx * 1000 / (cur.fs * cur.Th))}] TJ`);
    return out.join('\n');
  }

  function argObj(a) {
    if (a.t === 'num') return PDFNumber.of(a.v);
    if (a.t === 'name') return PDFName.of(a.v);
    return null;
  }
  const op = (name, args) => PDFOperator.of(name, args);
  const N = (v) => PDFNumber.of(+fmt(v));

  /**
   * Operators drawing the new text with the original font resource.
   * lines: [{ items, dx, dy }] — dx/dy = translation in user space for that line.
   * opts.rgb: [r,g,b] (0..1) overrides the original fill colour.
   */
  function drawOps(doc, an, m, lines, opts = {}) {
    const out = [];
    lines.forEach((ln) => {
      if (!ln.items.some((x) => x.bytes != null)) return;
      out.push(op('q'));
      if (Math.abs(ln.dx) > 1e-9 || Math.abs(ln.dy) > 1e-9) out.push(op('cm', [N(1), N(0), N(0), N(1), N(ln.dx), N(ln.dy)]));
      out.push(op('cm', m.ctm.map((v) => PDFNumber.of(v))));
      m.extg.forEach((a) => { const o = a.map(argObj).filter(Boolean); if (o.length) out.push(op('gs', o)); });
      if (m.lw != null) out.push(op('w', [PDFNumber.of(m.lw)]));
      m.stroke.forEach(([n, a]) => out.push(op(n, a.map(argObj).filter(Boolean))));
      if (opts.rgb) out.push(op('rg', opts.rgb.map((v) => N(v))));
      else m.fill.forEach(([n, a]) => out.push(op(n, a.map(argObj).filter(Boolean))));
      out.push(op('BT'));
      out.push(op('Tf', [PDFName.of(m.font), PDFNumber.of(m.fs)]));
      if (m.Tc) out.push(op('Tc', [PDFNumber.of(m.Tc)]));
      if (m.Tw) out.push(op('Tw', [PDFNumber.of(m.Tw)]));
      if (m.Th !== 1) out.push(op('Tz', [PDFNumber.of(m.Th * 100)]));
      if (m.Ts) out.push(op('Ts', [PDFNumber.of(m.Ts)]));
      if (m.Tr) out.push(op('Tr', [PDFNumber.of(m.Tr)]));
      out.push(op('Tm', m.Tm0.map((v) => PDFNumber.of(v))));
      const arr = PDFArray.withContext(doc.context);
      compact(ln.items).forEach((x) => arr.push(x.bytes != null ? PDFHexString.of(hexOf(x.bytes)) : N(x.num)));
      out.push(op('TJ', [arr]));
      out.push(op('ET'));
      out.push(op('Q'));
    });
    return out;
  }

  /** user-space translation for a viewport-space delta (dx, dy). */
  function vpDeltaToUser(T, dx, dy) {
    const t = inv(T);
    return [t[0] * dx + t[2] * dy, t[1] * dx + t[3] * dy];
  }

  window.TextEdit = { analyze, match, rewrite, setContent, layoutLine, minimalEdit, inlineOps, lineTm, drawOps, encodeChar, vpDeltaToUser, colorHex, _parseOps: parseOps, _mul: mul };
})();
