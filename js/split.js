/* Split / Extract pages tool */
(function () {
  'use strict';
  const { $, $$, el, icon, busy, toast, downloadBlob, baseName } = UI;
  const GROUP_COLORS = ['#16a34a', '#2563eb', '#db2777', '#ea580c', '#7c3aed', '#0891b2', '#ca8a04'];

  const S = { file: null, bytes: null, pdf: null, n: 0, picked: new Set(), thumbs: [] };

  function mode() {
    return $('input[name=smode]:checked').value;
  }

  /** "1-3, 5, 8-" → [[0,1,2],[4],[7..n-1]] (0-based). Throws on invalid input. */
  function parseRanges(str, n) {
    const out = [];
    str.replace(/[\u2010-\u2015\u2212]/g, '-').split(/[,;]+/).map((s) => s.trim()).filter(Boolean).forEach((part) => {
      const m = part.match(/^(\d*)\s*(?:-\s*(\d*))?$/);
      if (!m || (!m[1] && !m[2])) throw new Error(`"${part}" is not a valid range`);
      const isRange = part.includes('-');
      const a = m[1] ? +m[1] : 1;
      const b = isRange ? (m[2] ? +m[2] : n) : a;
      if (a > b) throw new Error(`"${part}": start page is after end page`);
      if (a < 1 || b > n) throw new Error(`"${part}": pages must be between 1 and ${n}`);
      const r = [];
      for (let i = a; i <= b; i++) r.push(i - 1);
      out.push(r);
    });
    return out;
  }

  function groups() {
    const n = S.n;
    const m = mode();
    if (m === 'each') return Array.from({ length: n }, (_, i) => [i]);
    if (m === 'every') {
      const k = Math.max(1, parseInt($('#splitN').value, 10) || 1);
      const g = [];
      for (let i = 0; i < n; i += k) g.push(Array.from({ length: Math.min(k, n - i) }, (_, j) => i + j));
      return g;
    }
    if (m === 'ranges') {
      const v = $('#splitRanges').value.trim();
      if (!v) return [];
      return parseRanges(v, n);
    }
    return S.picked.size ? [Array.from(S.picked).sort((a, b) => a - b)] : [];
  }

  function refresh() {
    const sum = $('#splitSummary');
    sum.classList.remove('err');
    let g = [];
    try {
      g = groups();
    } catch (err) {
      sum.textContent = err.message;
      sum.classList.add('err');
    }
    const m = mode();
    const pageGroup = new Map();
    g.forEach((grp, gi) => grp.forEach((p) => { if (!pageGroup.has(p)) pageGroup.set(p, gi); }));
    S.thumbs.forEach((th, i) => {
      const on = m === 'extract' && S.picked.has(i);
      th.classList.toggle('picked', on);
      th.setAttribute('aria-pressed', String(on));
      th.setAttribute('aria-disabled', String(m !== 'extract'));
      th.querySelector('.pick').hidden = m !== 'extract';
      const tag = th.querySelector('.grp');
      if (m !== 'extract' && pageGroup.has(i)) {
        const gi = pageGroup.get(i);
        tag.hidden = false;
        tag.textContent = `File ${gi + 1}`;
        tag.style.background = GROUP_COLORS[gi % GROUP_COLORS.length];
      } else {
        tag.hidden = true;
      }
    });
    if (!sum.classList.contains('err')) {
      if (!g.length) sum.textContent = m === 'extract' ? 'Click pages on the right to select them.' : 'Enter page ranges, e.g. 1-3, 5, 8-10.';
      else if (m === 'extract') sum.textContent = `${g[0].length} page${g[0].length > 1 ? 's' : ''} selected → 1 PDF`;
      else sum.textContent = `${S.n} pages → ${g.length} PDF file${g.length > 1 ? 's' : ''}${g.length > 1 ? ' (downloaded as ZIP)' : ''}`;
    }
    $('#splitGo').disabled = !g.length || sum.classList.contains('err');
    const label = m === 'extract' ? 'Extract pages' : 'Split PDF';
    $('#splitGoLabel').textContent = label;
    $('#splitGo').setAttribute('aria-label', label);
  }

  async function renderThumbs() {
    const wrap = $('#splitPages');
    wrap.innerHTML = '';
    S.thumbs = [];
    for (let i = 0; i < S.n; i++) {
      const th = el('button', 'thumb');
      th.type = 'button';
      th.setAttribute('aria-pressed', 'false');
      th.setAttribute('aria-label', `Page ${i + 1}`);
      th.innerHTML = `<span class="thumb-box"><canvas aria-hidden="true"></canvas><span class="grp" hidden></span><span class="pick" aria-hidden="true">${icon('check')}</span></span><span class="thumb-num" aria-hidden="true">${i + 1}</span>`;
      th.addEventListener('click', () => {
        // Selecting pages only applies to Extract mode; don't silently discard the chosen split mode.
        if (mode() !== 'extract') {
          toast('Choose “Extract selected pages” to pick individual pages.');
          return;
        }
        S.picked.has(i) ? S.picked.delete(i) : S.picked.add(i);
        refresh();
      });
      wrap.append(th);
      S.thumbs.push(th);
    }
    refresh();
    const pdf = S.pdf;
    for (let i = 0; i < S.n; i++) {
      if (S.pdf !== pdf) return;
      try {
        const page = await pdf.getPage(i + 1);
        const v1 = page.getViewport({ scale: 1 });
        const vp = page.getViewport({ scale: 300 / Math.max(v1.width, v1.height) });
        const c = S.thumbs[i].querySelector('canvas');
        c.width = vp.width;
        c.height = vp.height;
        await page.render({ canvasContext: c.getContext('2d'), viewport: vp }).promise;
      } catch (err) { console.warn(err); }
    }
  }

  async function open(file, initialMode) {
    busy('Opening PDF…');
    try {
      const bytes = new Uint8Array(await file.arrayBuffer());
      let pdf;
      try {
        pdf = await pdfjsLib.getDocument({ data: bytes.slice() }).promise;
      } catch (err) {
        throw new Error(err && err.name === 'PasswordException' ? 'This PDF is password-protected.' : 'That file doesn\'t look like a valid PDF.');
      }
      if (S.pdf) S.pdf.destroy();
      Object.assign(S, { file, bytes, pdf, n: pdf.numPages, picked: new Set() });
      $('#splitFileName').textContent = file.name;
      $('#splitTitle').textContent = initialMode === 'extract' ? 'Extract pages' : 'Split PDF';
      $(`input[name=smode][value=${initialMode === 'extract' ? 'extract' : 'each'}]`).checked = true;
      $('#splitRanges').value = '';
      document.body.dataset.view = 'split';
      renderThumbs();
      return true;
    } catch (err) {
      toast(err.message, 'error');
      return false;
    } finally {
      busy(false);
    }
  }

  async function run() {
    let g;
    try { g = groups(); } catch (err) { toast(err.message, 'error'); return; }
    if (!g.length) return;
    busy('Creating files…');
    try {
      const { PDFDocument } = PDFLib;
      let src;
      try {
        src = await PDFDocument.load(S.bytes);
      } catch (err) {
        if (err && /encrypt/i.test(err.name + ' ' + err.message)) {
          toast('This PDF is encrypted and can\'t be split in the browser.', 'error');
          return;
        }
        throw err;
      }
      if (src.isEncrypted) {
        toast('This PDF is encrypted and can\'t be split in the browser.', 'error');
        return;
      }
      const name = baseName(S.file.name);
      const outputs = [];
      for (const grp of g) {
        const out = await PDFDocument.create();
        const pages = await out.copyPages(src, grp);
        pages.forEach((p) => out.addPage(p));
        const label = grp.length === 1 ? `${grp[0] + 1}` : `${grp[0] + 1}-${grp[grp.length - 1] + 1}`;
        outputs.push({ name: `${name}-${mode() === 'extract' ? 'extracted' : 'pages-' + label}.pdf`, bytes: await out.save() });
      }
      if (outputs.length === 1) {
        downloadBlob(outputs[0].bytes, outputs[0].name);
      } else {
        const zip = new JSZip();
        const used = new Set();
        outputs.forEach((o) => {
          let n = o.name, c = 1;
          while (used.has(n)) n = o.name.replace(/\.pdf$/, ` (${++c}).pdf`);
          used.add(n);
          zip.file(n, o.bytes);
        });
        downloadBlob(await zip.generateAsync({ type: 'blob' }), `${name}-split.zip`);
      }
      toast(`Done — ${outputs.length} file${outputs.length > 1 ? 's' : ''} created.`, 'ok');
    } catch (err) {
      console.error(err);
      toast('Could not split the PDF: ' + err.message, 'error');
    } finally {
      busy(false);
    }
  }

  $$('input[name=smode]').forEach((r) => r.addEventListener('change', refresh));
  const selectMode = (v) => () => { $(`input[name=smode][value=${v}]`).checked = true; refresh(); };
  ['input', 'focus'].forEach((ev) => {
    $('#splitN').addEventListener(ev, selectMode('every'));
    $('#splitRanges').addEventListener(ev, selectMode('ranges'));
  });
  $('#splitGo').addEventListener('click', run);

  function close() {
    if (S.pdf) { try { S.pdf.destroy(); } catch (e) { /* ignore */ } }
    Object.assign(S, { file: null, bytes: null, pdf: null, n: 0, picked: new Set(), thumbs: [] });
    $('#splitPages').innerHTML = '';
  }

  window.Split = { open, close, parseRanges };
})();
