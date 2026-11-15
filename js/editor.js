/* Pagecraft editor: page rendering (pdf.js), interactive overlays (fabric.js), export (pdf-lib). */
(function () {
  'use strict';
  const { $, $$, el, icon, busy, toast, imageFileToDataURL, downloadBlob, isPdf, baseName } = UI;

  pdfjsLib.GlobalWorkerOptions.workerSrc = 'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js';

  const PROPS = ['kind', 'pdfFont', 'srcItem', 'imgRef'];
  const FONT_CSS = {
    Helvetica: 'Helvetica, Arial, sans-serif',
    Times: '"Times New Roman", Times, serif',
    Courier: '"Courier New", Courier, monospace',
  };
  const DRAG_TOOLS = ['rect', 'ellipse', 'line', 'whiteout', 'highlight'];
  const STICKY_TOOLS = ['draw', 'highlight'];
  const HL_COLORS = ['#ffe94d', '#86efac', '#f9a8d4', '#93c5fd', '#fdba74'];
  // fabric text layout constants (baseline offset from line top = fs * mult * (1 - fraction))
  const TEXT_MULT = fabric.Text.prototype._fontSizeMult;
  const TEXT_FRAC = fabric.Text.prototype._fontSizeFraction;

  // Replacement textboxes for original text runs never soft-wrap (a wrapped word would land on
  // the next original line); the box grows to fit its longest line instead.
  const _wrapText = fabric.Textbox.prototype._wrapText;
  fabric.Textbox.prototype._wrapText = function (lines, desiredWidth) {
    return _wrapText.call(this, lines, this.srcItem != null ? Infinity : desiredWidth);
  };
  const _initDims = fabric.Textbox.prototype.initDimensions;
  fabric.Textbox.prototype.initDimensions = function () {
    _initDims.call(this);
    if (this.srcItem != null && !this.__skipDimension && this._textLines) {
      const w = this.calcTextWidth();
      if (w > this.width) this._set('width', Math.ceil(w * 100) / 100 + 0.5);
    }
  };

  fabric.Object.prototype.set({
    transparentCorners: false,
    cornerColor: '#ffffff',
    cornerStrokeColor: '#2563eb',
    borderColor: '#2563eb',
    cornerSize: 10,
    cornerStyle: 'circle',
    borderScaleFactor: 1.5,
  });

  const E = {
    sources: new Map(),
    entries: [],
    order: [],
    zoom: 1,
    tool: 'select',
    history: [],
    future: [],
    fileName: 'document.pdf',
    dirty: false,
    current: null,
    clipboard: null,
    drag: null,
    imgs: new Map(), // imgRef -> data URL (history snapshots reference images by id)
    defaults: {
      text: { pdfFont: 'Helvetica', fontSize: 14, fill: '#111111', fontWeight: 'normal', fontStyle: 'normal', textAlign: 'left' },
      shape: { stroke: '#e11d48', fill: '', strokeWidth: 2, opacity: 1 },
      draw: { stroke: '#1d4ed8', strokeWidth: 3, opacity: 1 },
      highlight: { fill: HL_COLORS[0] },
      whiteout: { fill: '#ffffff' },
    },
  };
  let uid = 0;
  const nextId = () => ++uid;
  const ALL_SRC = new Map(); // srcId -> source, across every open document

  /* ---------- multiple documents (batch editing) ----------
   * Each open PDF is a document with its own pages, history and view state. The active
   * document's fields live directly on E (so the rest of the editor is unchanged); switching
   * documents swaps these fields in and out. */
  const DOC_KEYS = ['sources', 'entries', 'order', 'history', 'future', 'fileName', 'dirty', 'current', 'zoom'];
  E.docs = [];
  E.active = -1;

  /* =================================================================
   * Geometry
   * ================================================================= */
  // Affine matrices [a,b,c,d,e,f]; mul(A,B) = apply A, then B.
  function mul(m1, m2) {
    return [
      m1[0] * m2[0] + m1[1] * m2[2],
      m1[0] * m2[1] + m1[1] * m2[3],
      m1[2] * m2[0] + m1[3] * m2[2],
      m1[2] * m2[1] + m1[3] * m2[3],
      m1[4] * m2[0] + m1[5] * m2[2] + m2[4],
      m1[4] * m2[1] + m1[5] * m2[3] + m2[5],
    ];
  }
  function inv(m) {
    const d = m[0] * m[3] - m[1] * m[2];
    return [m[3] / d, -m[1] / d, -m[2] / d, m[0] / d, (m[2] * m[5] - m[3] * m[4]) / d, (m[1] * m[4] - m[0] * m[5]) / d];
  }
  function dispSize(e) {
    const r = e.rot % 180 !== 0;
    return { w: Math.round((r ? e.H : e.W) * E.zoom), h: Math.round((r ? e.W : e.H) * E.zoom) };
  }
  /** Base-viewport coords → screen pixels inside the page, incl. zoom and user rotation. */
  function vpt(e) {
    const z = E.zoom;
    switch (e.rot) {
      case 90: return [0, z, -z, 0, e.H * z, 0];
      case 180: return [-z, 0, 0, -z, e.W * z, e.H * z];
      case 270: return [0, -z, z, 0, 0, e.W * z];
      default: return [z, 0, 0, z, 0, 0];
    }
  }

  /* =================================================================
   * Loading
   * ================================================================= */
  async function loadSource(file) {
    const bytes = new Uint8Array(await file.arrayBuffer());
    let pdf;
    try {
      pdf = await pdfjsLib.getDocument({ data: bytes.slice() }).promise;
    } catch (err) {
      if (err && err.name === 'PasswordException') throw new Error(`"${file.name}" is password-protected. Please remove the password first.`);
      throw new Error(`"${file.name}" doesn't look like a valid PDF.`);
    }
    // pdf.js silently opens files that only carry an owner (permissions) password, but pdf-lib
    // cannot decrypt them and would write a broken file - refuse up front with a clear message.
    let pl = null;
    try {
      pl = await PDFLib.PDFDocument.load(bytes, { updateMetadata: false });
    } catch (err) {
      if ((PDFLib.EncryptedPDFError && err instanceof PDFLib.EncryptedPDFError) || /encrypted/i.test((err && err.message) || '')) {
        pdf.destroy();
        throw new Error(`"${file.name}" is protected with editing restrictions (a permissions password). Please remove the restrictions first, then open it again.`);
      }
      console.warn('pdf-lib could not parse this file', err);
    }
    const src = { id: nextId(), name: file.name, bytes, pdf };
    if (pl) src.pl = Promise.resolve(pl);
    E.sources.set(src.id, src);
    ALL_SRC.set(src.id, src);
    const list = [];
    for (let i = 0; i < pdf.numPages; i++) {
      const page = await pdf.getPage(i + 1);
      const vp = page.getViewport({ scale: 1 });
      list.push(makeEntry({ srcId: src.id, pageIndex: i, page, baseRot: page.rotate, W: vp.width, H: vp.height, T: vp.transform.slice() }));
    }
    return list;
  }

  function blankEntry(W, H) {
    return makeEntry({ blank: true, srcId: null, pageIndex: -1, baseRot: 0, W, H, T: [1, 0, 0, -1, 0, H] });
  }

  function srcOf(id) {
    return E.sources.get(id) || ALL_SRC.get(id);
  }

  async function getPage(e) {
    if (!e.page) e.page = await srcOf(e.srcId).pdf.getPage(e.pageIndex + 1);
    return e.page;
  }

  function disposeDoc(d) {
    d.entries.forEach((e) => {
      if (e.fc) e.fc.dispose();
      if (e.renderTask) e.renderTask.cancel();
      if (e.previewPdf) { try { e.previewPdf.destroy(); } catch (err) { /* already gone */ } e.previewPdf = null; }
    });
    d.sources.forEach((s) => { ALL_SRC.delete(s.id); try { s.pdf.destroy(); } catch (err) { /* gone */ } });
  }

  function reset() {
    saveActive();
    E.docs.forEach((d) => { if (d.sources !== E.sources) disposeDoc(d); });
    E.docs = [];
    E.active = -1;
    ALL_SRC.clear();
    E.entries.forEach((e) => {
      if (e.fc) e.fc.dispose();
      if (e.renderTask) e.renderTask.cancel();
      if (e.previewPdf) { try { e.previewPdf.destroy(); } catch (err) { /* already gone */ } e.previewPdf = null; }
    });
    E.imgs.clear();
    E.sources.forEach((s) => s.pdf.destroy());
    E.sources.clear();
    E.entries = [];
    E.order = [];
    E.history = [];
    E.future = [];
    E.current = null;
    E.dirty = false;
    E.tool = 'select';
    thumbQueue.length = 0;
    $('#pagesContainer').innerHTML = '';
    const sc = $('#pagesScroll');
    if (sc) { sc.scrollTop = 0; sc.scrollLeft = 0; }
    $('#thumbList').innerHTML = '';
    document.body.classList.remove('organize', 'mode-edittext', 'sidebar-open');
  }

  function newDocState() {
    E.sources = new Map();
    E.entries = [];
    E.order = [];
    E.history = [];
    E.future = [];
    E.dirty = false;
    E.current = null;
  }
  function snapshotDoc(fileName) {
    return {
      sources: E.sources, entries: E.entries, order: E.order, history: E.history, future: E.future,
      fileName, dirty: false, current: null, zoom: E.zoom, scrollTop: 0, fitted: false,
    };
  }
  /** Copy the live editor fields back into the active document. */
  function saveActive() {
    if (E.active < 0 || !E.docs[E.active]) return;
    const d = E.docs[E.active];
    DOC_KEYS.forEach((k) => { d[k] = E[k]; });
    const sc = $('#pagesScroll');
    if (sc && document.body.dataset.view === 'editor') d.scrollTop = sc.scrollTop;
  }
  /** Load a list of files as separate documents (failures are reported, not fatal). */
  async function loadDocs(files, fails) {
    const docs = [];
    for (let i = 0; i < files.length; i++) {
      if (files.length > 1) $('#busyMsg').textContent = `Opening ${i + 1} of ${files.length}…`;
      newDocState();
      try {
        E.order.push(...(await loadSource(files[i])));
        docs.push(snapshotDoc(files[i].name));
      } catch (err) {
        E.sources.forEach((src) => { ALL_SRC.delete(src.id); try { src.pdf.destroy(); } catch (e2) { /* gone */ } });
        fails.push(err.message || `Could not open “${files[i].name}”.`);
      }
    }
    return docs;
  }

  function clearSelections() {
    stopEditing();
    E.drag = null;
    E.order.forEach((e) => { if (e.fc && e.fc.getActiveObject()) { e.fc.discardActiveObject(); e.fc.requestRenderAll(); } });
  }

  /** Switch the editor to document i. dir: 'next' | 'prev' for the slide animation. */
  function activate(i, dir) {
    if (i < 0 || i >= E.docs.length || i === E.active) return;
    if (E.active >= 0) clearSelections();
    saveActive();
    E.active = i;
    const d = E.docs[i];
    DOC_KEYS.forEach((k) => { E[k] = d[k]; });
    $('#edFileName').textContent = E.fileName;
    document.title = `${E.fileName} — Pagecraft`;
    layout();
    const sc = $('#pagesScroll');
    if (!d.fitted) {
      d.fitted = true;
      sc.scrollTop = 0;
      fitWidth(true);
    } else {
      $('#zoomVal').textContent = Math.round(E.zoom * 100) + '%';
      sc.scrollTop = d.scrollTop || 0;
    }
    E.order.forEach((e) => { if (e.fc) applyTool(e); if (!e.thumbDone) { e.thumbDone = true; queueThumb(e); } });
    updateUndo();
    updateProps();
    renderDocBar();
    if (dir) {
      const pc = $('#pagesContainer');
      pc.classList.remove('slide-next', 'slide-prev');
      void pc.offsetWidth; // restart the animation
      pc.classList.add(dir === 'next' ? 'slide-next' : 'slide-prev');
    }
    scheduleRender();
  }
  function nextDoc() { activate(E.active + 1, 'next'); }
  function prevDoc() { activate(E.active - 1, 'prev'); }

  async function open(files, opts = {}) {
    files = Array.from(files || []).filter(isPdf);
    if (!files.length && !opts.blank) { toast('Please choose a PDF file.', 'error'); return false; }
    const batch = !!opts.batch && files.length > 1;
    busy(files.length > 1 ? 'Opening files…' : 'Opening PDF…');
    try {
      reset();
      let docs = [];
      const fails = [];
      if (opts.blank) {
        newDocState();
        E.order.push(blankEntry(595.28, 841.89));
        docs = [snapshotDoc('untitled.pdf')];
      } else if (batch) {
        docs = await loadDocs(files, fails);
        if (!docs.length) throw new Error(fails[0] || 'Could not open the files.');
      } else {
        newDocState();
        for (const f of files) E.order.push(...(await loadSource(f)));
        docs = [snapshotDoc(files.length > 1 ? 'merged.pdf' : files[0].name)];
      }
      E.docs = docs;
      E.active = -1;
      document.body.dataset.view = 'editor';
      activate(0);
      setTool('select');
      if (opts.organize) setOrganize(true);
      if (opts.tool === 'sign') setTimeout(() => setTool('sign'), 50);
      if (batch) toast(`${docs.length} PDFs opened as separate documents — swipe or use the arrows to switch, then “Download all”.`, 'ok', 6000);
      else if (files.length > 1) toast(`${files.length} files combined — drag pages to reorder, then apply changes.`, 'ok', 5000);
      fails.forEach((m) => toast(m, 'error', 8000));
      return true;
    } catch (err) {
      console.error(err);
      toast(err.message || 'Could not open the file.', 'error');
      return false;
    } finally {
      busy(false);
    }
  }

  /** Add more PDFs as separate documents to the current workspace. */
  async function addDocs(files) {
    files = UI.filterPdfs ? await UI.filterPdfs(files) : Array.from(files || []).filter(isPdf);
    if (!files.length) { toast('Please choose a PDF file.', 'error'); return; }
    busy('Opening files…');
    try {
      clearSelections();
      saveActive();
      const prev = E.active;
      const fails = [];
      const docs = await loadDocs(files, fails);
      E.docs.push(...docs);
      E.active = -1;
      // restore the previous document's fields first (loadDocs left the last new doc on E)
      activate(docs.length ? E.docs.length - docs.length : prev, docs.length ? 'next' : undefined);
      if (docs.length) toast(`Added ${docs.length} document${docs.length > 1 ? 's' : ''}.`, 'ok');
      fails.forEach((m) => toast(m, 'error', 8000));
    } finally {
      busy(false);
    }
  }

  function closeDoc(i) {
    const d = E.docs[i];
    if (!d || E.docs.length < 2) return;
    const dirty = i === E.active ? hasChanges() : d.dirty;
    if (dirty && !confirm(`Close “${d.fileName}”? Its changes haven't been downloaded.`)) return;
    if (i === E.active) {
      clearSelections();
      saveActive();
      E.active = -1;
      disposeDoc(d);
      E.docs.splice(i, 1);
      activate(Math.min(i, E.docs.length - 1));
    } else {
      disposeDoc(d);
      E.docs.splice(i, 1);
      if (i < E.active) E.active--;
      renderDocBar();
    }
  }

  /** Run fn with document d's fields swapped onto E (no DOM changes). */
  async function withDoc(d, fn) {
    saveActive();
    const live = {};
    DOC_KEYS.forEach((k) => { live[k] = E[k]; });
    DOC_KEYS.forEach((k) => { E[k] = d[k]; });
    try {
      return await fn();
    } finally {
      DOC_KEYS.forEach((k) => { d[k] = E[k]; E[k] = live[k]; });
    }
  }

  async function downloadAll() {
    if (!E.docs.length) return;
    clearSelections();
    busy('Preparing ZIP…');
    try {
      saveActive();
      const zip = new JSZip();
      const used = new Map();
      const problems = [];
      const done = [];
      for (let i = 0; i < E.docs.length; i++) {
        const d = E.docs[i];
        $('#busyMsg').textContent = `Saving ${i + 1} of ${E.docs.length}…`;
        try {
          const { bytes } = await withDoc(d, buildPdf);
          let name = baseName(d.fileName) + '.pdf';
          const n = used.get(name.toLowerCase()) || 0;
          used.set(name.toLowerCase(), n + 1);
          if (n) name = `${baseName(d.fileName)} (${n + 1}).pdf`;
          zip.file(name, bytes);
          done.push(d);
        } catch (err) {
          console.error(err);
          problems.push(`${d.fileName}: ${err.message || err}`);
        }
      }
      if (!done.length) throw new Error(problems[0] || 'Nothing to save.');
      $('#busyMsg').textContent = 'Compressing…';
      downloadBlob(await zip.generateAsync({ type: 'blob' }), 'edited-pdfs.zip');
      done.forEach((d) => { d.dirty = false; });
      if (done.includes(E.docs[E.active])) E.dirty = false;
      renderDocBar();
      toast(`ZIP with ${done.length} PDF${done.length > 1 ? 's' : ''} is downloading.`, 'ok');
      problems.forEach((m) => toast('Not included — ' + m, 'error', 9000));
    } catch (err) {
      toast('Could not create the ZIP: ' + (err.message || err), 'error');
    } finally {
      busy(false);
    }
  }

  function renderDocBar() {
    const bar = $('#docBar');
    const multi = E.docs.length > 1;
    bar.hidden = !multi;
    document.body.classList.toggle('multi-doc', multi);
    if (!multi) return;
    const tabs = $('#docTabs');
    tabs.replaceChildren(...E.docs.map((d, i) => {
      const dirty = i === E.active ? E.dirty : d.dirty;
      const b = el('button', 'doc-tab' + (i === E.active ? ' on' : '') + (dirty ? ' dirty' : ''));
      b.dataset.i = i;
      b.title = d.fileName;
      b.setAttribute('role', 'tab');
      b.setAttribute('aria-selected', i === E.active ? 'true' : 'false');
      b.innerHTML = `<span class="dot" title="Edited"></span><span class="nm"></span><span class="pg">${d.order.length}p</span><span class="x" data-close title="Close">${icon('x')}</span>`;
      b.querySelector('.nm').textContent = baseName(d.fileName);
      return b;
    }));
    $('#docCount').textContent = `${E.active + 1} / ${E.docs.length}`;
    $('#docPrev').disabled = E.active <= 0;
    $('#docNext').disabled = E.active >= E.docs.length - 1;
    const on = tabs.querySelector('.doc-tab.on');
    if (on) {
      const tr = on.getBoundingClientRect(), br = tabs.getBoundingClientRect();
      if (tr.left < br.left || tr.right > br.right) tabs.scrollLeft += tr.left - br.left - br.width / 2 + tr.width / 2;
    }
  }
  function updateDocDirty() {
    const on = $('#docTabs .doc-tab.on');
    if (on) on.classList.toggle('dirty', !!E.dirty);
  }

  async function addFiles(files) {
    files = UI.filterPdfs ? await UI.filterPdfs(files) : Array.from(files || []).filter(isPdf);
    if (!files.length) { toast('Please choose a PDF file.', 'error'); return; }
    busy('Adding pages…');
    try {
      const before = snapPages();
      const added = [];
      for (const f of files) added.push(...(await loadSource(f)));
      E.order.push(...added);
      pushHistory({ type: 'pages', before, after: snapPages() });
      layout();
      added.forEach(queueThumb);
      if (!document.body.classList.contains('organize')) scrollToEntry(added[0]);
      toast(`Added ${added.length} page${added.length > 1 ? 's' : ''}.`, 'ok');
    } catch (err) {
      toast(err.message || 'Could not add that file.', 'error');
    } finally {
      busy(false);
    }
  }

  /* =================================================================
   * Page entries & DOM
   * ================================================================= */
  function makeEntry(o) {
    const e = Object.assign({ id: nextId(), rot: 0, fc: null, renderedKey: null, textItems: null }, o);
    const page = el('div', 'page');
    const inner = el('div', 'page-inner');
    const pc = el('canvas', 'pdf-canvas');
    const fcEl = el('canvas');
    const tl = el('div', 'textlayer');
    inner.append(pc, fcEl, tl);
    const label = el('div', 'page-label');
    page.append(inner, label);
    Object.assign(e, { el: page, inner, pdfCanvas: pc, fabEl: fcEl, textLayer: tl, labelEl: label });
    inner.addEventListener('pointerdown', () => setCurrent(e), true);
    tl.addEventListener('click', (ev) => {
      const s = ev.target.closest('span[data-i]');
      if (s) convertTextItem(e, e.textItems[+s.dataset.i]);
    });

    // thumbnail
    const th = el('div', 'thumb');
    th.draggable = true;
    th.innerHTML = `<div class="thumb-box"><canvas></canvas><div class="thumb-actions">
      <button data-act="rotl" title="Rotate left">${icon('rotl')}</button>
      <button data-act="rotr" title="Rotate right">${icon('rotr')}</button>
      <button data-act="dup" title="Duplicate page">${icon('copy')}</button>
      <button data-act="blank" title="Insert blank page after">${icon('plus')}</button>
      <button data-act="del" title="Delete page">${icon('trash')}</button>
    </div></div><div class="thumb-num"></div>`;
    e.thumb = th;
    e.thumbCanvas = th.querySelector('canvas');
    e.thumbNum = th.querySelector('.thumb-num');
    th.addEventListener('click', (ev) => {
      const b = ev.target.closest('button[data-act]');
      if (b) { ev.stopPropagation(); thumbAction(e, b.dataset.act); return; }
      if (document.body.classList.contains('organize')) return;
      scrollToEntry(e);
      document.body.classList.remove('sidebar-open');
    });
    th.addEventListener('dblclick', () => {
      if (document.body.classList.contains('organize')) { setOrganize(false); scrollToEntry(e); }
    });
    bindThumbDnD(e);
    E.entries.push(e);
    return e;
  }

  function layout() {
    $('#pagesContainer').replaceChildren(...E.order.map((e) => e.el));
    $('#thumbList').replaceChildren(...E.order.map((e) => e.thumb));
    E.order.forEach((e, i) => {
      e.labelEl.textContent = `Page ${i + 1}`;
      e.thumbNum.textContent = i + 1;
      sizeEntry(e);
    });
    $('#pageCount').textContent = E.order.length;
    if (!E.order.includes(E.current)) E.current = null;
    if (!E.current && E.order.length) setCurrent(E.order[0]);
    else updateIndicator();
    scheduleRender();
  }

  function sizeEntry(e) {
    const { w, h } = dispSize(e);
    e.inner.style.width = w + 'px';
    e.inner.style.height = h + 'px';
    const m = vpt(e);
    if (e.fc) {
      e.fc.setDimensions({ width: w, height: h });
      e.fc.setViewportTransform(m);
      e.fc.calcOffset();
    }
    e.textLayer.style.width = e.W + 'px';
    e.textLayer.style.height = e.H + 'px';
    e.textLayer.style.transform = `matrix(${m.join(',')})`;
  }

  /* ---------- rendering ---------- */
  let renderRaf = 0;
  function scheduleRender() {
    if (renderRaf) return;
    renderRaf = requestAnimationFrame(() => { renderRaf = 0; renderVisible(); });
  }

  function renderVisible() {
    if (document.body.dataset.view !== 'editor' || document.body.classList.contains('organize')) return;
    const sc = $('#pagesScroll');
    const vr = sc.getBoundingClientRect();
    let best = null, bestD = Infinity;
    const far = Math.max(2700, vr.height * 3);
    for (const e of E.order) {
      const r = e.el.getBoundingClientRect();
      if (r.bottom > vr.top - 900 && r.top < vr.bottom + 900) {
        renderEntry(e);
        if (E.tool === 'edittext') ensureTextLayer(e);
      } else if (r.bottom < vr.top - far || r.top > vr.bottom + far) {
        releaseEntry(e);
      }
      const d = Math.abs((r.top + r.bottom) / 2 - (vr.top + vr.height * 0.4));
      if (d < bestD) { bestD = d; best = e; }
    }
    if (best && best !== E.current && !E.scrollLock) setCurrent(best);
  }

  /** Free the page bitmap of a page far outside the viewport (re-rendered when it comes back). */
  function releaseEntry(e) {
    if (!e.renderedKey && !e.renderTask) return;
    if (e.renderTask) { try { e.renderTask.cancel(); } catch (err) { /* noop */ } e.renderTask = null; }
    e.renderedKey = null;
    e.pdfCanvas.width = 0;
    e.pdfCanvas.height = 0;
  }

  const MAX_RENDER_PX = 16e6; // keep each page bitmap well under browser canvas limits
  async function renderEntry(e) {
    ensureFabric(e);
    const key = E.zoom + '|' + e.rot;
    if (e.renderedKey === key) return;
    e.renderedKey = key;
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const c = e.pdfCanvas;
    if (e.blank) {
      const { w, h } = dispSize(e);
      c.width = w; c.height = h;
      const cx = c.getContext('2d');
      cx.fillStyle = '#fff';
      cx.fillRect(0, 0, w, h);
      return;
    }
    const page = await getPage(e);
    const scale = Math.min(E.zoom * dpr, Math.sqrt(MAX_RENDER_PX / Math.max(1, e.W * e.H)));
    const vp = page.getViewport({ scale, rotation: (e.baseRot + e.rot) % 360 });
    if (e.renderTask) e.renderTask.cancel();
    const off = document.createElement('canvas');
    off.width = Math.floor(vp.width);
    off.height = Math.floor(vp.height);
    const task = page.render({ canvasContext: off.getContext('2d'), viewport: vp });
    e.renderTask = task;
    try {
      await task.promise;
    } catch (err) {
      if (err && err.name === 'RenderingCancelledException') return;
      console.error(err);
      if (e.renderedKey === key) e.renderedKey = null;
      return;
    }
    if (e.renderTask === task) e.renderTask = null;
    if (e.renderedKey !== key) return;
    c.width = off.width;
    c.height = off.height;
    c.getContext('2d').drawImage(off, 0, 0);
  }

  /* ---------- thumbnails ---------- */
  const thumbQueue = [];
  let thumbBusy = false;
  function queueThumb(e) {
    if (!thumbQueue.includes(e)) thumbQueue.push(e);
    pumpThumbs();
  }
  async function pumpThumbs() {
    if (thumbBusy) return;
    thumbBusy = true;
    while (thumbQueue.length) {
      const e = thumbQueue.shift();
      try { await renderThumb(e); } catch (err) { console.warn(err); }
    }
    thumbBusy = false;
  }
  async function renderThumb(e) {
    const c = e.thumbCanvas;
    const r = e.rot % 180 !== 0;
    const bw = r ? e.H : e.W, bh = r ? e.W : e.H;
    const s = 340 / Math.max(bw, bh);
    if (e.blank) {
      c.width = Math.round(bw * s); c.height = Math.round(bh * s);
      const cx = c.getContext('2d');
      cx.fillStyle = '#fff';
      cx.fillRect(0, 0, c.width, c.height);
      return;
    }
    const page = await getPage(e);
    const vp = page.getViewport({ scale: s, rotation: (e.baseRot + e.rot) % 360 });
    const off = document.createElement('canvas');
    off.width = Math.floor(vp.width);
    off.height = Math.floor(vp.height);
    await page.render({ canvasContext: off.getContext('2d'), viewport: vp }).promise;
    c.width = off.width;
    c.height = off.height;
    c.getContext('2d').drawImage(off, 0, 0);
  }

  /* ---------- current page ---------- */
  function setCurrent(e) {
    if (!e || E.current === e) return;
    if (E.current) {
      E.current.el.classList.remove('current');
      E.current.thumb.classList.remove('active');
    }
    E.current = e;
    e.el.classList.add('current');
    e.thumb.classList.add('active');
    const tl = $('#thumbList');
    const tr = e.thumb.getBoundingClientRect(), lr = tl.getBoundingClientRect();
    if (!document.body.classList.contains('organize') && (tr.top < lr.top || tr.bottom > lr.bottom)) {
      tl.scrollTop += tr.top - lr.top - lr.height / 2 + tr.height / 2;
    }
    updateIndicator();
  }
  function updateIndicator() {
    const i = E.order.indexOf(E.current);
    $('#pageIndicator').textContent = `${i + 1} / ${E.order.length}`;
  }
  function scrollToEntry(e) {
    if (!e) return;
    const sc = $('#pagesScroll');
    E.scrollLock = true;
    setCurrent(e);
    sc.scrollTo({ top: e.el.offsetTop - 20, behavior: 'smooth' });
    clearTimeout(E.scrollLockT);
    E.scrollLockT = setTimeout(() => { E.scrollLock = false; }, 700);
  }

  /* =================================================================
   * Fabric canvases
   * ================================================================= */
  function ensureFabric(e) {
    if (e.fc) return e.fc;
    const { w, h } = dispSize(e);
    const fc = new fabric.Canvas(e.fabEl, {
      width: w,
      height: h,
      preserveObjectStacking: true,
      selectionColor: 'rgba(37,99,235,0.08)',
      selectionBorderColor: '#2563eb',
      selectionLineWidth: 1,
      stopContextMenu: true,
      fireRightClick: false,
    });
    e.fc = fc;
    fc.setViewportTransform(vpt(e));
    bindCanvas(e);
    applyTool(e);
    if (e.pendingJSON) {
      const json = e.pendingJSON;
      e.pendingJSON = null;
      e.restoring = true;
      e.loadingJSON = json;
      // resolves once every object (incl. asynchronously decoded images) is on the canvas
      e.ready = new Promise((res) => {
        fc.loadFromJSON(hydrate(json), () => {
          e.restoring = false;
          e.loadingJSON = null;
          fc.setViewportTransform(vpt(e));
          fc.renderAll();
          e.lastJSON = serialize(e);
          refreshTextLayer(e);
          res();
        });
      });
    } else {
      e.lastJSON = serialize(e);
      e.ready = Promise.resolve();
    }
    return fc;
  }

  /** Canvas JSON with images stored by reference (keeps undo snapshots small). */
  function serialize(e) {
    const j = e.fc.toJSON(PROPS);
    (j.objects || []).forEach((o) => { if (o.type === 'image' && o.imgRef && E.imgs.has(o.imgRef)) o.src = 'pcimg:' + o.imgRef; });
    return JSON.stringify(j);
  }
  /** Resolve image references of a serialize() snapshot back to their data URLs. */
  function hydrate(json) {
    if (typeof json !== 'string' || json.indexOf('"pcimg:') < 0) return json;
    const j = JSON.parse(json);
    (j.objects || []).forEach((o) => {
      if (o.type === 'image' && typeof o.src === 'string' && o.src.startsWith('pcimg:')) o.src = E.imgs.get(o.src.slice(6)) || '';
    });
    return j;
  }
  function imageRef(url) {
    for (const [k, v] of E.imgs) if (v === url) return k;
    const k = 'i' + nextId();
    E.imgs.set(k, url);
    return k;
  }

  function bindCanvas(e) {
    const fc = e.fc;
    fc.on('mouse:down', (o) => onDown(e, o));
    fc.on('mouse:move', (o) => onMove(e, o));
    fc.on('mouse:up', () => onUp(e));
    fc.on('object:modified', (o) => {
      const t = o.target;
      if (t && t.type === 'activeSelection') {
        if (t.scaleX !== 1 || t.scaleY !== 1 || t.skewX || t.skewY) {
          // release the group so its transform lands on the children, then bake each one's scale
          const objs = t.getObjects();
          fc.discardActiveObject();
          objs.forEach(normalize);
          fc.setActiveObject(new fabric.ActiveSelection(objs, { canvas: fc }));
          fc.requestRenderAll();
        }
      } else {
        normalize(t);
      }
      commit(e);
      updateProps();
    });
    fc.on('path:created', (o) => {
      // brush opacity is baked into an rgba colour; move it to the object's opacity
      const c = new fabric.Color(o.path.stroke || '#000000');
      const a = c.getAlpha();
      o.path.set({ kind: 'draw' });
      if (a < 1) o.path.set({ opacity: a, stroke: '#' + c.toHex() });
      commit(e);
    });
    fc.on('text:changed', () => { E.dirty = true; });
    fc.on('text:editing:exited', (o) => {
      const t = o.target;
      // an emptied replacement box stays (empty) so the original text stays deleted;
      // a new, empty text box is simply dropped
      if (!t.text.trim()) {
        if (t.srcItem != null) { if (t.text !== '') t.set('text', ''); } else fc.remove(t);
      }
      commit(e);
      updateProps();
    });
    const onSel = () => {
      E.order.forEach((x) => {
        if (x !== e && x.fc && x.fc.getActiveObject()) { x.fc.discardActiveObject(); x.fc.requestRenderAll(); }
      });
      setCurrent(e);
      updateProps();
    };
    fc.on('selection:created', onSel);
    fc.on('selection:updated', onSel);
    fc.on('selection:cleared', () => updateProps());
  }

  function applyTool(e) {
    const fc = e.fc, t = E.tool;
    if (!fc) return;
    const sel = t === 'select' || t === 'edittext';
    fc.isDrawingMode = t === 'draw';
    if (t === 'draw') {
      const b = new fabric.PencilBrush(fc);
      b.color = withAlpha(E.defaults.draw.stroke, E.defaults.draw.opacity);
      b.width = E.defaults.draw.strokeWidth;
      b.decimate = 1.5;
      fc.freeDrawingBrush = b;
    }
    fc.selection = sel;
    fc.skipTargetFind = !sel;
    fc.defaultCursor = sel ? 'default' : t === 'text' ? 'text' : 'crosshair';
    fc.hoverCursor = sel ? 'move' : fc.defaultCursor;
    if (!sel) fc.discardActiveObject();
    fc.requestRenderAll();
  }

  function withAlpha(hex, a) {
    if (a == null || a >= 1) return hex;
    const c = new fabric.Color(hex);
    c.setAlpha(a);
    return c.toRgba();
  }

  /* ---------- creation by click/drag ---------- */
  /** Clear selections (and end text editing) on every page except e. */
  function clearOtherSelections(e) {
    E.order.forEach((x) => {
      if (x === e || !x.fc) return;
      const a = x.fc.getActiveObject();
      if (!a) return;
      if (a.isEditing) a.exitEditing();
      x.fc.discardActiveObject();
      x.fc.requestRenderAll();
    });
  }

  /** Base-viewport vectors for one screen pixel right (ux) / down (uy), scaled to 1 base unit. */
  function screenDirs(e) {
    const m = fabric.util.invertTransform(vpt(e));
    const z = E.zoom;
    const ux = fabric.util.transformPoint(new fabric.Point(1, 0), m, true);
    const uy = fabric.util.transformPoint(new fabric.Point(0, 1), m, true);
    return { ux: { x: ux.x * z, y: ux.y * z }, uy: { x: uy.x * z, y: uy.y * z } };
  }
  /** Axis-aligned base-coord box that appears on screen as sw x sh with its top-left at p. */
  function screenBox(e, p, sw, sh) {
    const { ux, uy } = screenDirs(e);
    const xs = [p.x, p.x + ux.x * sw, p.x + uy.x * sh, p.x + ux.x * sw + uy.x * sh];
    const ys = [p.y, p.y + ux.y * sw, p.y + uy.y * sh, p.y + ux.y * sw + uy.y * sh];
    const left = Math.min(...xs), top = Math.min(...ys);
    return { left, top, width: Math.max(...xs) - left, height: Math.max(...ys) - top };
  }

  function onDown(e, o) {
    clearOtherSelections(e);
    setCurrent(e);
    const t = E.tool;
    const p = e.fc.getPointer(o.e);
    if (t === 'text') {
      addText(e, p);
      return;
    }
    if (!DRAG_TOOLS.includes(t)) return;
    let obj;
    const d = E.defaults;
    const base = { left: p.x, top: p.y, strokeUniform: true, objectCaching: false };
    if (t === 'rect') obj = new fabric.Rect({ ...base, width: 1, height: 1, kind: 'rect', stroke: d.shape.stroke, fill: d.shape.fill || '', strokeWidth: d.shape.strokeWidth, opacity: d.shape.opacity });
    else if (t === 'ellipse') obj = new fabric.Ellipse({ ...base, rx: 0.5, ry: 0.5, kind: 'ellipse', stroke: d.shape.stroke, fill: d.shape.fill || '', strokeWidth: d.shape.strokeWidth, opacity: d.shape.opacity });
    else if (t === 'line') obj = new fabric.Line([p.x, p.y, p.x, p.y], { strokeUniform: true, kind: 'line', stroke: d.shape.stroke, strokeWidth: Math.max(1, d.shape.strokeWidth), strokeLineCap: 'round', opacity: d.shape.opacity });
    else if (t === 'whiteout') obj = new fabric.Rect({ ...base, width: 1, height: 1, kind: 'whiteout', fill: d.whiteout.fill, strokeWidth: 0 });
    else if (t === 'highlight') obj = new fabric.Rect({ ...base, width: 1, height: 1, kind: 'highlight', fill: d.highlight.fill, strokeWidth: 0, opacity: 0.4 });
    E.drag = { e, obj, start: p, tool: t };
    e.fc.add(obj);
  }

  function onMove(e, o) {
    const dr = E.drag;
    if (!dr || dr.e !== e) return;
    const p = e.fc.getPointer(o.e);
    const s = dr.start, obj = dr.obj;
    const x = Math.min(s.x, p.x), y = Math.min(s.y, p.y), w = Math.abs(p.x - s.x), h = Math.abs(p.y - s.y);
    if (dr.tool === 'line') obj.set({ x2: p.x, y2: p.y });
    else if (dr.tool === 'ellipse') obj.set({ left: x, top: y, rx: w / 2, ry: h / 2 });
    else obj.set({ left: x, top: y, width: w, height: h });
    obj.setCoords();
    e.fc.requestRenderAll();
  }

  function onUp(e) {
    const dr = E.drag;
    if (!dr || dr.e !== e) return;
    E.drag = null;
    const obj = dr.obj;
    const s = dr.start;
    if (dr.tool === 'line') {
      if (Math.hypot(obj.x2 - obj.x1, obj.y2 - obj.y1) < Math.max(4, 4 / E.zoom)) {
        const { ux } = screenDirs(e);
        obj.set({ x2: s.x + ux.x * 120, y2: s.y + ux.y * 120 });
      }
    } else {
      // default size on a click; a thin drag (e.g. along a line of text) keeps its length
      // and gets a sensible thickness, centred on the drag line
      const [dw, dh] = { ellipse: [100, 64], highlight: [140, 16], whiteout: [140, 22] }[dr.tool] || [120, 70];
      const thick = Math.min(dw, dh);
      const w = obj.getScaledWidth(), h = obj.getScaledHeight();
      const thr = Math.max(4, 4 / E.zoom); // ~4 screen pixels
      let box = null;
      if (w < thr && h < thr) box = screenBox(e, s, dw, dh);
      else if (h < thr) box = { left: obj.left, top: obj.top + h / 2 - thick / 2, width: w, height: thick };
      else if (w < thr) box = { left: obj.left + w / 2 - thick / 2, top: obj.top, width: thick, height: h };
      if (box) {
        if (dr.tool === 'ellipse') obj.set({ left: box.left, top: box.top, rx: box.width / 2, ry: box.height / 2 });
        else obj.set(box);
      }
    }
    obj.set({ objectCaching: true });
    obj.setCoords();
    if (!STICKY_TOOLS.includes(dr.tool)) setTool('select');
    e.fc.setActiveObject(obj);
    e.fc.requestRenderAll();
    commit(e);
    updateProps();
  }

  function addText(e, p) {
    const d = E.defaults.text;
    // on a user-rotated page the box is counter-rotated so it reads horizontally on screen
    const { uy } = screenDirs(e);
    const off = d.fontSize * 0.7;
    const tb = new fabric.Textbox('Text', {
      left: p.x - uy.x * off,
      top: p.y - uy.y * off,
      angle: e.rot ? 360 - e.rot : 0,
      width: Math.max(80, d.fontSize * 10),
      fontSize: d.fontSize,
      fontFamily: FONT_CSS[d.pdfFont],
      pdfFont: d.pdfFont,
      fontWeight: d.fontWeight,
      fontStyle: d.fontStyle,
      textAlign: d.textAlign,
      fill: d.fill,
      kind: 'text',
      splitByGrapheme: false,
    });
    e.fc.add(tb);
    setTool('select');
    e.fc.setActiveObject(tb);
    tb.enterEditing();
    tb.selectAll();
    e.fc.requestRenderAll();
  }

  /** Bake scale into dimensions so stroke widths and font sizes stay true. */
  function normalize(o) {
    if (!o || o.type === 'activeSelection') return;
    if (o.scaleX === 1 && o.scaleY === 1) return;
    if (o.type === 'line') {
      // bake the transform into the end points so the (uniform) stroke exports at its true width
      const p = o.calcLinePoints();
      const m = o.calcTransformMatrix();
      const a = fabric.util.transformPoint(new fabric.Point(p.x1, p.y1), m);
      const b = fabric.util.transformPoint(new fabric.Point(p.x2, p.y2), m);
      o.set({ angle: 0, scaleX: 1, scaleY: 1, skewX: 0, skewY: 0, flipX: false, flipY: false });
      o.set({ x1: a.x, y1: a.y, x2: b.x, y2: b.y });
    } else if (o.type === 'rect') o.set({ width: o.width * o.scaleX, height: o.height * o.scaleY, scaleX: 1, scaleY: 1 });
    else if (o.type === 'ellipse') o.set({ rx: o.rx * o.scaleX, ry: o.ry * o.scaleY, scaleX: 1, scaleY: 1 });
    else if (o.type === 'textbox') {
      const s = o.scaleY;
      o.set({ fontSize: Math.max(2, Math.round(o.fontSize * s * 10) / 10), width: o.width * o.scaleX, scaleX: 1, scaleY: 1 });
    }
    o.setCoords();
  }

  /* ---------- images & signatures ---------- */
  function visibleCenter(e) {
    const ir = e.inner.getBoundingClientRect();
    const vr = $('#pagesScroll').getBoundingClientRect();
    const x0 = Math.max(ir.left, vr.left), x1 = Math.min(ir.right, vr.right);
    const y0 = Math.max(ir.top, vr.top), y1 = Math.min(ir.bottom, vr.bottom);
    const sx = (x0 < x1 ? (x0 + x1) / 2 : (ir.left + ir.right) / 2) - ir.left;
    const sy = (y0 < y1 ? (y0 + y1) / 2 : (ir.top + ir.bottom) / 2) - ir.top;
    return fabric.util.transformPoint(new fabric.Point(sx, sy), fabric.util.invertTransform(vpt(e)));
  }

  function placeImage(url, kind, maxW) {
    const e = E.current || E.order[0];
    if (!e) return;
    ensureFabric(e);
    const imgRef = imageRef(url);
    fabric.Image.fromURL(url, (img) => {
      if (!img || !img.width) { toast('Could not load that image.', 'error'); return; }
      const r = e.rot % 180 !== 0;
      const pw = r ? e.H : e.W, ph = r ? e.W : e.H; // page size as seen on screen
      const s = Math.min(1, (maxW || pw * 0.5) / img.width, (ph * 0.5) / img.height);
      const c = visibleCenter(e);
      img.set({ kind, imgRef, scaleX: s, scaleY: s, angle: e.rot ? 360 - e.rot : 0 });
      img.setPositionByOrigin(new fabric.Point(c.x, c.y), 'center', 'center');
      e.fc.add(img);
      setTool('select');
      e.fc.setActiveObject(img);
      e.fc.requestRenderAll();
      commit(e);
      updateProps();
    });
  }

  /* ---------- source page / content-stream analysis (TextEdit) ---------- */
  const previewPages = new WeakSet();
  /** The ORIGINAL pdf.js page (never the edited preview copy). */
  async function srcPdfPage(e) {
    if (!e.origPage) {
      e.origPage = e.page && !previewPages.has(e.page) ? e.page : await srcOf(e.srcId).pdf.getPage(e.pageIndex + 1);
    }
    return e.origPage;
  }
  function plSource(srcId) {
    const s = srcOf(srcId);
    if (!s.pl) s.pl = PDFLib.PDFDocument.load(s.bytes, { updateMetadata: false });
    return s.pl;
  }
  function pageAnalysis(e) {
    const s = srcOf(e.srcId);
    if (!s.te) s.te = new Map();
    if (!s.te.has(e.pageIndex)) {
      s.te.set(e.pageIndex, (async () => {
        try {
          const d = await plSource(e.srcId);
          return TextEdit.analyze(d, d.getPage(e.pageIndex));
        } catch (err) {
          console.warn('Content analysis failed', err);
          return { ok: false, reason: err.message || String(err), glyphs: [] };
        }
      })());
    }
    return s.te.get(e.pageIndex);
  }
  /** Locate the run's glyphs in the content stream (cached on the run). */
  async function editInfo(e, ti) {
    if (!ti.te) {
      ti.te = (async () => {
        try {
          const an = await pageAnalysis(e);
          const m = TextEdit.match(an, { x0: ti.x, x1: ti.x + ti.w, baseline: ti.baseline, fs: ti.fs, str: ti.str }, e.T);
          if (!m.ok) console.info('Text edit falls back to cover box:', m.reason);
          return m;
        } catch (err) {
          console.warn(err);
          return { ok: false, reason: err.message };
        }
      })();
    }
    return ti.te;
  }
  /** Is pdf.js' embedded FontFace loaded and does it hold glyphs for every char of str? */
  function faceCovers(name, str) {
    try {
      if (!name || !document.fonts) return false;
      let loaded = false;
      document.fonts.forEach((f) => { if (f.family.replace(/["']/g, '') === name && f.status === 'loaded') loaded = true; });
      if (!loaded) return false;
      const c = faceCovers.ctx || (faceCovers.ctx = document.createElement('canvas').getContext('2d'));
      for (const ch of new Set(Array.from(str.replace(/\s/g, '')))) {
        c.font = `40px "${name}", monospace`;
        const a = c.measureText(ch).width;
        c.font = `40px "${name}", serif`;
        if (Math.abs(a - c.measureText(ch).width) > 0.01) return false;
      }
      return true;
    } catch (err) {
      return false;
    }
  }
  /** Style the replacement Textbox starts with (also the reference for "unchanged"). */
  function initStyle(e, ti, m) {
    if (ti.init) return ti.init;
    const g = guessFont(e, ti);
    const native = !!(m && m.ok && m.native);
    const face = native && faceCovers(ti.fontName, ti.str);
    const fontSize = native ? ti.fs : Math.round(ti.fs * 10) / 10;
    const x = native ? m.originVp[0] : ti.x;
    const base = native ? m.originVp[1] : ti.baseline;
    ti.init = {
      native, face, guess: g, pdfFont: g.pdfFont, fontSize,
      fontFamily: face ? `"${ti.fontName}", ${FONT_CSS[g.pdfFont]}` : FONT_CSS[g.pdfFont],
      fontWeight: face ? 'normal' : g.fontWeight,
      fontStyle: face ? 'normal' : g.fontStyle,
      fill: (m && m.ok && m.color) || sampleColor(e, ti),
      left: x,
      top: base - fontSize * TEXT_MULT * (1 - TEXT_FRAC),
    };
    return ti.init;
  }

  /* =================================================================
   * Edit existing text
   * ================================================================= */
  async function loadTextItems(e) {
    if (e.textItems) return e.textItems;
    if (e.textItemsP) return e.textItemsP;
    e.textItemsP = (async () => {
      const page = await srcPdfPage(e);
      const tc = await page.getTextContent();
      const vp = page.getViewport({ scale: 1 });
      const runs = [];
      for (const it of tc.items) {
        if (!it.str || !it.str.trim()) continue; // spacer items would bridge table cells
        const tx = pdfjsLib.Util.transform(vp.transform, it.transform);
        // only upright horizontal text
        if (!(tx[0] > 0) || Math.abs(tx[1]) > 1e-3 * tx[0] || Math.abs(tx[2]) > 1e-3 * tx[0]) continue;
        const fs = Math.abs(tx[3]);
        if (fs < 1) continue;
        const st = tc.styles[it.fontName] || {};
        const asc = st.ascent || 0.8, desc = st.descent || -0.2;
        const item = {
          str: it.str, x: tx[4], baseline: tx[5], w: it.width, fs, fontName: it.fontName, family: st.fontFamily || '',
          asc, desc,
        };
        const prev = runs[runs.length - 1];
        const gap = prev ? item.x - (prev.x + prev.w) : 0;
        if (prev && Math.abs(prev.baseline - item.baseline) < fs * 0.2 && Math.abs(prev.fs - fs) < 0.5
          && prev.fontName === item.fontName && gap > -fs * 0.3 && gap < fs * 0.8) {
          const needSpace = gap > fs * 0.15 && !/\s$/.test(prev.str) && !/^\s/.test(item.str);
          prev.str += (needSpace ? ' ' : '') + item.str;
          prev.w = item.x + item.w - prev.x;
        } else if (it.str.trim()) {
          runs.push(item);
        }
      }
      e.textItems = runs
        .map((r) => {
          const lead = r.str.length - r.str.trimStart().length;
          r.str = r.str.trim();
          if (lead) { const cw = r.w / (r.str.length + lead); r.x += cw * lead; r.w -= cw * lead; }
          return r;
        })
        .filter((r) => r.str && r.w > 0)
        .map((r, i) => Object.assign(r, { gi: i, y: r.baseline - r.fs * r.asc, h: r.fs * (r.asc - r.desc) }));
      return e.textItems;
    })();
    try {
      return await e.textItemsP;
    } finally {
      e.textItemsP = null;
    }
  }

  async function ensureTextLayer(e) {
    if (e.blank) return;
    if (!e.textItems) {
      if (e.textLoading) return;
      e.textLoading = true;
      try {
        await loadTextItems(e);
      } catch (err) {
        console.warn('Text extraction failed', err);
        return;
      } finally {
        e.textLoading = false;
      }
    }
    if (!e.textLayerBuilt) {
      e.textLayerBuilt = true;
      e.textLayer.replaceChildren(...e.textItems.map((r, i) => {
        const s = el('span');
        s.dataset.i = i;
        s.title = 'Click to edit this text';
        Object.assign(s.style, { left: r.x + 'px', top: r.y + 'px', width: r.w + 'px', height: r.h + 'px' });
        return s;
      }));
    }
    refreshTextLayer(e);
  }

  /** Replacement textboxes on this page that stand in for an original text run. */
  function textObjs(e) {
    return e.fc ? e.fc.getObjects().filter((o) => o.kind === 'text' && o.srcItem != null) : [];
  }

  function refreshTextLayer(e) {
    if (e.textItems && e.textLayerBuilt) {
      const used = new Set();
      if (e.fc) e.fc.getObjects().forEach((o) => { if (o.srcItem != null) used.add(o.srcItem); });
      Array.from(e.textLayer.children).forEach((s) => s.classList.toggle('used', used.has(+s.dataset.i)));
    }
    syncTextPreview(e).catch((err) => console.warn('Preview update failed', err));
  }

  /**
   * Keep the page canvas in sync with in-place edits: the page is re-rendered from a
   * single-page copy whose content stream no longer contains the replaced glyphs.
   * Derived purely from the fabric objects, so undo/redo restore the original glyphs.
   */
  async function syncTextPreview(e) {
    if (e.blank || !e.fc) return;
    const objs = textObjs(e);
    if (!objs.length && !e.previewSig) return;
    if (objs.length) await loadTextItems(e);
    const runs = [];
    for (const o of objs) {
      const ti = e.textItems && e.textItems[o.srcItem];
      if (!ti) continue;
      const m = await editInfo(e, ti);
      if (m && m.ok) {
        runs.push(ti);
        warnFallback(e, o, ti, m);
      }
    }
    const sig = [...new Set(runs.map((t) => t.gi))].sort((a, b) => a - b).join(',');
    if (sig === (e.previewSig || '')) return;
    e.previewSig = sig;
    const token = (e.previewToken = (e.previewToken || 0) + 1);
    const orig = await srcPdfPage(e);
    let page = orig, pdf = null;
    if (sig) {
      try {
        const an = await pageAnalysis(e);
        const glyphs = [];
        for (const ti of runs) glyphs.push(...(await editInfo(e, ti)).glyphs);
        const src = await plSource(e.srcId);
        const d = await PDFLib.PDFDocument.create();
        const [cp] = await d.copyPages(src, [e.pageIndex]);
        d.addPage(cp);
        TextEdit.setContent(d, cp, TextEdit.rewrite(an, glyphs));
        const bytes = await d.save();
        pdf = await pdfjsLib.getDocument({ data: bytes }).promise;
        page = await pdf.getPage(1);
        previewPages.add(page);
      } catch (err) {
        console.warn('Could not build edited preview', err);
        page = orig;
      }
    }
    if (token !== e.previewToken) { if (pdf) pdf.destroy(); return; }
    const old = e.previewPdf;
    e.previewPdf = pdf;
    e.page = page;
    e.renderedKey = null;
    if (E.order.includes(e)) { renderEntry(e); queueThumb(e); }
    if (old) setTimeout(() => old.destroy(), 5000);
  }

  /** Lay out a textbox's lines with the run's original font (null if a char is missing). */
  function nativeLines(an, m, o) {
    const lines = o.textLines.map((s, i) => TextEdit.layoutLine(an, m, s, i === 0));
    const missing = [...new Set(lines.flatMap((l) => l.missing))];
    return { lines, missing };
  }

  function warnFallback(e, o, ti, m) {
    if (!m.native || o.__teWarned === o.text) return;
    o.__teWarned = o.text;
    pageAnalysis(e).then((an) => {
      const { missing } = nativeLines(an, m, o);
      if (missing.length) {
        const init = initStyle(e, ti, m);
        toast(`The original font doesn't contain “${missing.join(' ')}”, so this text will be saved in ${init.pdfFont} instead.`, 'error', 7000);
      }
    }).catch(() => {});
  }

  const SANS_RE = /sans|grotesk|gothic|helvet|arial|verdana|tahoma|calibri|candara|corbel|segoe|roboto|futura|avenir|frutiger|univers|gotham|myriad|lato|inter\b|franklin|gill|trebuchet|din\b|montserrat|poppins|nunito|source ?sans|ubuntu|noto ?sans|lucida ?grande|geneva|aptos|sf ?pro/;
  const SERIF_RE = /times|serif|georgia|garamond|cambria|minion|palatino|palladio|baskerville|bodoni|caslon|book ?antiqua|bookman|schoolbook|didot|charter|merriweather|playfair|constantia|cochin|hoefler|new ?york|sabon|plantin|utopia|tinos|liberation ?serif|nimbus ?rom|cmr\d|lmroman|perpetua|goudy/;
  function guessFont(e, ti) {
    let name = '', fo = null;
    try {
      const p = e.origPage || e.page;
      const objs = p && p.commonObjs;
      if (objs && objs.has(ti.fontName)) { fo = objs.get(ti.fontName); name = (fo && fo.name) || ''; }
    } catch (err) { /* font not resolved */ }
    // 'Roman' / 'Book' are weights (HelveticaNeue-Roman, Avenir-Book), not serif markers
    const n = name.replace(/^[A-Z]{6}\+/, '').toLowerCase();
    let pdfFont = 'Helvetica';
    if (/courier|mono|consol|menlo|typewriter/.test(n) || (fo && fo.isMonospace) || (!n && ti.family === 'monospace')) pdfFont = 'Courier';
    else if (SANS_RE.test(n)) pdfFont = 'Helvetica';
    else if (SERIF_RE.test(n) || (fo && fo.isSerifFont) || ti.family === 'serif') pdfFont = 'Times';
    return {
      pdfFont,
      fontWeight: (fo && (fo.bold || fo.black)) || /bold|black|heavy|semibold|demi/.test(n) ? 'bold' : 'normal',
      fontStyle: (fo && fo.italic) || /italic|oblique/.test(n) ? 'italic' : 'normal',
    };
  }

  /**
   * Measure a text run from an offscreen render of just its region in the BASE viewport at a
   * fixed high resolution (independent of zoom and of the user's page rotation): background
   * colour (exact, not bucketed), ink colour (farthest from the background, so light text on
   * dark fills works) and a cover box limited to the run's own ink - stopping at horizontal and
   * vertical rules and at ink belonging to neighbouring lines.
   */
  async function measureRun(e, ti) {
    if (ti.meas !== undefined) return ti.meas;
    ti.meas = null;
    try {
      const page = e.page || (await srcPdfPage(e));
      const fs = ti.fs;
      const bx0 = ti.x - fs * 0.4, bx1 = ti.x + ti.w + fs * 0.4;
      const by0 = ti.baseline - fs * 1.3, by1 = ti.baseline + fs * 0.6;
      const K = Math.max(1, Math.min(4, 4000 / (bx1 - bx0), 1200 / (by1 - by0)));
      const w = Math.ceil((bx1 - bx0) * K), h = Math.ceil((by1 - by0) * K);
      if (w < 4 || h < 4) return null;
      const cv = document.createElement('canvas');
      cv.width = w; cv.height = h;
      const cx = cv.getContext('2d', { willReadFrequently: true });
      const vp = page.getViewport({ scale: K });
      await page.render({ canvasContext: cx, viewport: vp, transform: [1, 0, 0, 1, -bx0 * K, -by0 * K] }).promise;
      const d = cx.getImageData(0, 0, w, h).data;
      // background: most common 5-bit bucket, then the exact mean of the pixels in it
      const counts = new Map();
      for (let i = 0; i < d.length; i += 4) {
        const key = ((d[i] >> 3) << 10) | ((d[i + 1] >> 3) << 5) | (d[i + 2] >> 3);
        counts.set(key, (counts.get(key) || 0) + 1);
      }
      let bgKey = 0, bgN = -1;
      counts.forEach((n, key) => { if (n > bgN) { bgN = n; bgKey = key; } });
      const acc = [0, 0, 0];
      let an = 0;
      for (let i = 0; i < d.length; i += 4) {
        if ((((d[i] >> 3) << 10) | ((d[i + 1] >> 3) << 5) | (d[i + 2] >> 3)) === bgKey) { acc[0] += d[i]; acc[1] += d[i + 1]; acc[2] += d[i + 2]; an++; }
      }
      const bg = acc.map((v) => Math.round(v / Math.max(1, an)));
      const dist = (i) => Math.abs(d[i] - bg[0]) + Math.abs(d[i + 1] - bg[1]) + Math.abs(d[i + 2] - bg[2]);
      const ink = (x, y) => dist((y * w + x) * 4) > 60;
      const px = (v) => Math.round((v - bx0) * K), py = (v) => Math.round((v - by0) * K);
      const cx0 = Math.max(0, px(ti.x)), cx1 = Math.min(w - 1, px(ti.x + ti.w));
      const baseRow = Math.min(h - 1, Math.max(0, py(ti.baseline)));
      const rowInkAll = (y) => { let n = 0; for (let x = 0; x < w; x++) if (ink(x, y)) n++; return n; };
      const rowInk = (y, a, b) => { let n = 0; for (let x = a; x <= b; x++) if (ink(x, y)) n++; return n; };
      const isHRule = (y) => rowInkAll(y) > w * 0.85;
      // vertical band: from the run's baseline out to its font's ascent/descent, stopping at rules
      // and, away from the baseline, at the first empty row (ink beyond it is another line's)
      const asc = Math.min(1.05, Math.max(0.7, ti.asc || 0.8)), desc = Math.min(0.35, Math.max(0.15, -(ti.desc || -0.2)));
      const upLim = Math.max(0, py(ti.baseline - fs * (asc + 0.05)));
      const dnLim = Math.min(h - 1, py(ti.baseline + fs * (desc + 0.05)));
      const solid = py(ti.baseline - fs * 0.45); // x-height region is always part of the run
      // (small gaps are tolerated so i-dots and accents stay with their glyphs)
      const gap = Math.max(1, Math.round(fs * 0.1 * K));
      let top = baseRow, bot = baseRow;
      for (let y = baseRow - 1; y >= upLim && !isHRule(y); y--) {
        if (y >= solid || rowInk(y, cx0, cx1) > 0) top = y;
        else if (top - y > gap) break;
      }
      for (let y = baseRow + 1; y <= dnLim && !isHRule(y); y++) {
        if (rowInk(y, cx0, cx1) > 0) bot = y;
        else if (y - bot > gap) break;
      }
      // vertical rules just outside the run (cell borders) bound the box horizontally
      const isVRule = (x) => { let n = 0; for (let y = top; y <= bot; y++) if (ink(x, y)) n++; return n >= (bot - top + 1) * 0.85; };
      const slack = Math.round(fs * 0.12 * K);
      let L = Math.max(0, cx0 - slack), R = Math.min(w - 1, cx1 + slack);
      for (let x = cx0 - 1; x >= L; x--) if (isVRule(x)) { L = x + 1; break; }
      for (let x = cx1 + 1; x <= R; x++) if (isVRule(x)) { R = x - 1; break; }
      let ix0 = w, ix1 = -1, iy0 = h, iy1 = -1, far = 0;
      for (let y = top; y <= bot; y++) {
        for (let x = L; x <= R; x++) {
          const i = (y * w + x) * 4;
          const dd = dist(i);
          if (dd > 60) {
            if (x < ix0) ix0 = x; if (x > ix1) ix1 = x;
            if (y < iy0) iy0 = y; if (y > iy1) iy1 = y;
          }
          if (dd > far) far = dd;
        }
      }
      const hex = (c) => '#' + c.map((v) => Math.max(0, Math.min(255, Math.round(v))).toString(16).padStart(2, '0')).join('');
      // ink colour: mean of the pixels closest to "full ink" (anti-aliased edges blend into bg)
      let inkHex = null;
      if (far > 60) {
        const s3 = [0, 0, 0];
        let k = 0;
        for (let y = top; y <= bot; y++) for (let x = L; x <= R; x++) {
          const i = (y * w + x) * 4;
          if (dist(i) >= far * 0.85) { s3[0] += d[i]; s3[1] += d[i + 1]; s3[2] += d[i + 2]; k++; }
        }
        inkHex = hex(s3.map((v) => v / k));
      }
      let box = null;
      if (ix1 >= 0) {
        // ~0.5pt margin for anti-aliasing, never across other ink or a rule
        const m = Math.max(1, Math.round(K * 0.5));
        let y0 = iy0, y1 = iy1, x0 = ix0, x1 = ix1;
        for (let k = 0; k < m && y0 - 1 >= 0 && !isHRule(y0 - 1) && rowInk(y0 - 1, L, R) === 0; k++) y0--;
        for (let k = 0; k < m && y1 + 1 < h && !isHRule(y1 + 1) && rowInk(y1 + 1, L, R) === 0; k++) y1++;
        x0 = Math.max(L, x0 - m); x1 = Math.min(R, x1 + m);
        box = { x: bx0 + x0 / K, y: by0 + y0 / K, w: (x1 - x0 + 1) / K, h: (y1 - y0 + 1) / K, bg: hex(bg) };
      }
      ti.meas = { box, bg: hex(bg), ink: inkHex };
    } catch (err) {
      console.warn('Could not measure text run', err);
      ti.meas = null;
    }
    return ti.meas;
  }

  /** Sample the darkest pixel in the run's area to guess the ink color. */
  function sampleColor(e, ti) {
    if (ti.meas && ti.meas.ink) return ti.meas.ink;
    try {
      if (e.rot !== 0 || !e.renderedKey) return '#000000';
      const c = e.pdfCanvas;
      const k = c.width / e.W;
      const x = Math.max(0, Math.floor(ti.x * k)), y = Math.max(0, Math.floor(ti.y * k));
      const w = Math.min(c.width - x, Math.ceil(ti.w * k)), h = Math.min(c.height - y, Math.ceil(ti.h * k));
      if (w < 1 || h < 1) return '#000000';
      const d = c.getContext('2d').getImageData(x, y, w, h).data;
      let best = 765, rgb = [0, 0, 0];
      for (let i = 0; i < d.length; i += 4) {
        const s = d[i] + d[i + 1] + d[i + 2];
        if (d[i + 3] > 200 && s < best) { best = s; rgb = [d[i], d[i + 1], d[i + 2]]; }
      }
      if (best > 600) return '#000000';
      return '#' + rgb.map((v) => v.toString(16).padStart(2, '0')).join('');
    } catch (err) {
      return '#000000';
    }
  }

  /**
   * Measure the real ink of a text run on the rendered page so the cover box hugs the
   * glyphs, never crosses table rules / neighbouring lines, and matches the background.
   */
  function coverBox(e, ti) {
    if (ti.meas && ti.meas.box) return ti.meas.box;
    const fallback = { x: ti.x - 0.5, y: ti.baseline - ti.fs * 0.78, w: ti.w + 1, h: ti.fs * 1.0, bg: '#ffffff' };
    try {
      if (e.rot !== 0 || !e.renderedKey) return fallback;
      const c = e.pdfCanvas;
      const k = c.width / e.W;
      // search area: the run's box plus a little slack
      const sx0 = Math.max(0, Math.floor((ti.x - ti.fs * 0.2) * k));
      const sx1 = Math.min(c.width, Math.ceil((ti.x + ti.w + ti.fs * 0.2) * k));
      const sy0 = Math.max(0, Math.floor((ti.baseline - ti.fs * 1.1) * k));
      const sy1 = Math.min(c.height, Math.ceil((ti.baseline + ti.fs * 0.45) * k));
      const w = sx1 - sx0, h = sy1 - sy0;
      if (w < 2 || h < 2) return fallback;
      const d = c.getContext('2d', { willReadFrequently: true }).getImageData(sx0, sy0, w, h).data;
      // background = most common colour in the area
      const counts = new Map();
      for (let i = 0; i < d.length; i += 4) {
        const key = ((d[i] >> 3) << 10) | ((d[i + 1] >> 3) << 5) | (d[i + 2] >> 3);
        counts.set(key, (counts.get(key) || 0) + 1);
      }
      let bgKey = 0, bgN = -1;
      counts.forEach((n, key) => { if (n > bgN) { bgN = n; bgKey = key; } });
      const bg = [((bgKey >> 10) & 31) * 8 + 4, ((bgKey >> 5) & 31) * 8 + 4, (bgKey & 31) * 8 + 4];
      const isInk = (i) => Math.abs(d[i] - bg[0]) + Math.abs(d[i + 1] - bg[1]) + Math.abs(d[i + 2] - bg[2]) > 90;
      // rows that are mostly ink across the whole width are rules (table borders, underlines)
      const rowInk = new Array(h).fill(0);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (isInk((y * w + x) * 4)) rowInk[y]++;
      const isRule = (y) => rowInk[y] > w * 0.85;
      // grow from the baseline row outwards, stopping at rules
      const baseRow = Math.min(h - 1, Math.max(0, Math.round(ti.baseline * k) - sy0));
      let top = baseRow, bot = baseRow;
      const glyphTop = Math.round((ti.baseline - ti.fs * 0.95) * k) - sy0;
      const glyphBot = Math.round((ti.baseline + ti.fs * 0.3) * k) - sy0;
      while (top - 1 >= Math.max(0, glyphTop) && !isRule(top - 1)) top--;
      while (bot + 1 <= Math.min(h - 1, glyphBot) && !isRule(bot + 1)) bot++;
      // tight ink box inside that band
      let ix0 = w, ix1 = -1, iy0 = h, iy1 = -1;
      for (let y = top; y <= bot; y++) {
        for (let x = 0; x < w; x++) {
          if (isInk((y * w + x) * 4)) {
            if (x < ix0) ix0 = x; if (x > ix1) ix1 = x;
            if (y < iy0) iy0 = y; if (y > iy1) iy1 = y;
          }
        }
      }
      if (ix1 < 0) return fallback;
      // limit horizontally to the run's own extent (don't eat neighbouring cells)
      const rx0 = Math.round((ti.x - ti.fs * 0.1) * k) - sx0, rx1 = Math.round((ti.x + ti.w + ti.fs * 0.1) * k) - sx0;
      ix0 = Math.max(ix0, rx0); ix1 = Math.min(ix1, rx1);
      const m = Math.max(1, Math.round(k * 0.6)); // ~0.6pt margin, kept inside the rule band
      const y0 = Math.max(top, iy0 - m), y1 = Math.min(bot, iy1 + m);
      const x0 = ix0 - m, x1 = ix1 + m;
      return {
        x: (sx0 + x0) / k, y: (sy0 + y0) / k, w: (x1 - x0 + 1) / k, h: (y1 - y0 + 1) / k,
        bg: '#' + bg.map((v) => Math.min(255, v).toString(16).padStart(2, '0')).join(''),
      };
    } catch (err) {
      return fallback;
    }
  }

  async function convertTextItem(e, ti) {
    if (!ti || e.converting) return;
    const fc = ensureFabric(e);
    const existing = textObjs(e).find((o) => o.srcItem === ti.gi);
    if (existing) {
      fc.setActiveObject(existing);
      if (!existing.text) { existing.enterEditing(); }
      fc.requestRenderAll(); updateProps(); return;
    }
    e.converting = true;
    let m = null;
    try {
      m = await editInfo(e, ti);
      if (!m || !m.ok || !m.color) await measureRun(e, ti);
    } finally {
      e.converting = false;
    }
    if (textObjs(e).some((o) => o.srcItem === ti.gi)) return;
    const st = initStyle(e, ti, m);
    const objs = [];
    if (!m || !m.ok) {
      // Fallback only: the glyphs couldn't be located precisely in the content stream
      // (form XObject, Type3 font, unknown metrics…), so cover them instead.
      const box = coverBox(e, ti);
      const bg = /^#(f[ef]){3}$/i.test(box.bg) ? '#ffffff' : box.bg; // only snap (all channels >= 254) to pure white
      objs.push(new fabric.Rect({
        left: box.x, top: box.y, width: box.w, height: box.h,
        fill: bg, strokeWidth: 0, kind: 'whiteout', srcItem: ti.gi, objectCaching: false,
      }));
    }
    const tb = new fabric.Textbox(ti.str, {
      left: st.left,
      top: st.top,
      width: ti.w * 1.1 + st.fontSize,
      fontSize: st.fontSize,
      fontFamily: st.fontFamily,
      pdfFont: st.pdfFont,
      fontWeight: st.fontWeight,
      fontStyle: st.fontStyle,
      fill: st.fill,
      kind: 'text',
      srcItem: ti.gi,
    });
    objs.push(tb);
    fc.add(...objs);
    commit(e);
    fc.setActiveObject(tb);
    tb.enterEditing();
    tb.selectAll();
    fc.requestRenderAll();
    updateProps();
  }

  /* =================================================================
   * Tools
   * ================================================================= */
  function setTool(t) {
    if (t === 'image') { const inp = $('#imageInput'); inp.value = ''; inp.click(); return; }
    if (t === 'sign') {
      Signature.open().then((url) => { if (url) placeImage(url, 'signature', 180); });
      return;
    }
    if (t === 'shapes') t = E.lastShape || 'rect';
    E.tool = t;
    $$('#toolbar .tool').forEach((b) => {
      const bt = b.dataset.tool;
      b.classList.toggle('on', bt === t || (bt === 'shapes' && ['rect', 'ellipse', 'line'].includes(t)));
    });
    document.body.classList.toggle('mode-edittext', t === 'edittext');
    E.order.forEach((e) => e.fc && applyTool(e));
    if (t === 'edittext') scheduleRender();
    updateProps();
  }

  /* =================================================================
   * Properties bar
   * ================================================================= */
  function activeObj() {
    for (const e of E.order) {
      const o = e.fc && e.fc.getActiveObject();
      if (o) return { e, o };
    }
    return null;
  }
  function kindOf(o) {
    if (!o) return null;
    if (o.type === 'activeSelection') return 'multi';
    if (o.kind) return o.kind;
    return { textbox: 'text', image: 'image', path: 'draw', line: 'line', ellipse: 'ellipse' }[o.type] || 'rect';
  }
  function groupOf(kind) {
    return { text: 'text', rect: 'shape', ellipse: 'shape', line: 'shape', draw: 'draw', highlight: 'highlight', whiteout: 'whiteout' }[kind];
  }
  const FIELDS = {
    text: ['font', 'size', 'style', 'align', 'fill'],
    rect: ['stroke', 'fillOpt', 'strokeWidth', 'opacity'],
    ellipse: ['stroke', 'fillOpt', 'strokeWidth', 'opacity'],
    line: ['stroke', 'strokeWidth', 'opacity'],
    draw: ['stroke', 'strokeWidth', 'opacity'],
    highlight: ['hl'],
    whiteout: ['fill'],
    image: ['opacity'],
    signature: ['opacity'],
    multi: [],
  };
  const HINTS = {
    select: 'Click an element on the page to select it. Use the toolbar to add text, images, signatures and more.',
    edittext: 'Click any text on the page to edit it. Highlighted boxes show editable text.',
    text: 'Click anywhere on a page to add text.',
    whiteout: 'Drag over content to cover it with a white box.',
    highlight: 'Drag over text to highlight it.',
    draw: 'Draw freehand on the page.',
    rect: 'Drag on the page to draw a rectangle.',
    ellipse: 'Drag on the page to draw an ellipse.',
    line: 'Drag on the page to draw a line.',
  };

  function updateProps() {
    const bar = $('#propsBar');
    const a = activeObj();
    const o = a && a.o;
    const kind = o ? kindOf(o) : (FIELDS[E.tool] ? E.tool : null);
    const g = groupOf(kind);
    const v = o || (g ? E.defaults[g] : null);
    let html = '';
    if (!kind || (!o && !FIELDS[kind].length)) {
      html = `<span class="hint">${HINTS[E.tool] || HINTS.select}</span>`;
    } else {
      if (!o && HINTS[E.tool]) html += `<span class="hint">${HINTS[E.tool]}</span><span class="vsep"></span>`;
      const fields = FIELDS[kind] || [];
      const getFont = () => (o ? o.pdfFont : v.pdfFont) || 'Helvetica';
      fields.forEach((f) => {
        switch (f) {
          case 'font':
            html += `<div class="group"><select data-p="font" title="Font">
              ${['Helvetica', 'Times', 'Courier'].map((n) => `<option value="${n}" ${getFont() === n ? 'selected' : ''}>${{ Helvetica: 'Helvetica (Sans)', Times: 'Times (Serif)', Courier: 'Courier (Mono)' }[n]}</option>`).join('')}
            </select></div>`;
            break;
          case 'size':
            html += `<div class="group"><input type="number" data-p="size" min="4" max="300" step="0.5" value="${+(v.fontSize).toFixed(1)}" title="Font size"></div>`;
            break;
          case 'style':
            html += `<div class="seg"><button data-p="bold" class="${v.fontWeight === 'bold' ? 'on' : ''}" title="Bold">${icon('bold')}</button><button data-p="italic" class="${v.fontStyle === 'italic' ? 'on' : ''}" title="Italic">${icon('italic')}</button></div>`;
            break;
          case 'align':
            html += `<div class="seg">${['left', 'center', 'right'].map((al) => `<button data-p="align" data-v="${al}" class="${(v.textAlign || 'left') === al ? 'on' : ''}" title="Align ${al}">${icon('align' + al[0])}</button>`).join('')}</div>`;
            break;
          case 'fill':
            html += `<div class="group"><label class="lbl">Color</label><input type="color" data-p="fill" value="${toHex(v.fill, '#000000')}"></div>`;
            break;
          case 'stroke':
            html += `<div class="group"><label class="lbl">${kind === 'draw' || kind === 'line' ? 'Color' : 'Border'}</label><input type="color" data-p="stroke" value="${toHex(v.stroke, '#000000')}"></div>`;
            break;
          case 'fillOpt': {
            const has = v.fill && v.fill !== 'transparent';
            html += `<div class="group"><label class="lbl">Fill</label><input type="color" data-p="fillOpt" value="${toHex(has ? v.fill : '#ffffff')}" ${has ? '' : 'style="opacity:.35"'}><label class="lbl"><input type="checkbox" data-p="noFill" ${has ? '' : 'checked'}> None</label></div>`;
            break;
          }
          case 'strokeWidth':
            html += `<div class="group"><label class="lbl">Width</label><input type="range" data-p="strokeWidth" min="${kind === 'rect' || kind === 'ellipse' ? 0 : 1}" max="24" step="1" value="${v.strokeWidth}"></div>`;
            break;
          case 'opacity':
            html += `<div class="group"><label class="lbl">Opacity</label><input type="range" data-p="opacity" min="10" max="100" step="5" value="${Math.round((v.opacity == null ? 1 : v.opacity) * 100)}"></div>`;
            break;
          case 'hl':
            html += `<div class="group"><label class="lbl">Color</label><div class="swatches">${HL_COLORS.map((c) => `<button class="sw ${toHex(v.fill) === c ? 'on' : ''}" data-p="hl" data-v="${c}" style="--c:${c}"></button>`).join('')}</div></div>`;
            break;
        }
      });
    }
    if (o) {
      html += `<span class="spacer"></span>
        <button class="pbtn" data-act="front" title="Bring to front">${icon('front')}<span>Front</span></button>
        <button class="pbtn" data-act="dup" title="Duplicate (Ctrl+D)">${icon('copy')}<span>Duplicate</span></button>
        <button class="pbtn danger" data-act="del" title="Delete (Del)">${icon('trash')}<span>Delete</span></button>`;
    }
    bar.innerHTML = html;
  }

  function toHex(c, fallback) {
    if (!c || c === 'transparent') return fallback || '#000000';
    try { return '#' + new fabric.Color(c).toHex().toLowerCase(); } catch (e) { return fallback || '#000000'; }
  }

  function setProp(p, val, commitNow) {
    const a = activeObj();
    const o = a && a.o && a.o.type !== 'activeSelection' ? a.o : null;
    const kind = o ? kindOf(o) : E.tool;
    const g = groupOf(kind);
    const d = g ? E.defaults[g] : {};
    const patch = {};
    switch (p) {
      case 'font': patch.pdfFont = val; patch.fontFamily = FONT_CSS[val]; d.pdfFont = val; break;
      case 'size': { const n = parseFloat(val); if (!(n > 0)) return; patch.fontSize = n; d.fontSize = n; break; }
      case 'bold': { const cur = o ? o.fontWeight : d.fontWeight; patch.fontWeight = d.fontWeight = cur === 'bold' ? 'normal' : 'bold'; break; }
      case 'italic': { const cur = o ? o.fontStyle : d.fontStyle; patch.fontStyle = d.fontStyle = cur === 'italic' ? 'normal' : 'italic'; break; }
      case 'align': patch.textAlign = d.textAlign = val; break;
      case 'fill': patch.fill = d.fill = val; break;
      case 'hl': patch.fill = d.fill = val; break;
      case 'stroke': patch.stroke = d.stroke = val; break;
      case 'fillOpt': patch.fill = d.fill = val; break;
      case 'noFill': patch.fill = d.fill = val ? '' : '#ffffff'; break;
      case 'strokeWidth': patch.strokeWidth = d.strokeWidth = +val; break;
      case 'opacity': patch.opacity = +val / 100; if (g) d.opacity = patch.opacity; break;
    }
    if (o) {
      if (o.type === 'textbox') o.styles = {};
      if (o.type === 'path' && 'fill' in patch) delete patch.fill;
      o.set(patch);
      if (o.type === 'textbox') o.initDimensions();
      o.setCoords();
      a.e.fc.requestRenderAll();
      if (commitNow) commit(a.e);
    } else if (E.tool === 'draw') {
      E.order.forEach((e) => e.fc && applyTool(e));
    }
  }

  function bindProps() {
    const bar = $('#propsBar');
    bar.addEventListener('input', (ev) => {
      const t = ev.target;
      if (!t.dataset.p || t.type === 'checkbox') return;
      setProp(t.dataset.p, t.value, false);
    });
    bar.addEventListener('change', (ev) => {
      const t = ev.target;
      if (!t.dataset.p) return;
      setProp(t.dataset.p, t.type === 'checkbox' ? t.checked : t.value, true);
      if (t.tagName === 'SELECT' || t.type === 'checkbox') updateProps();
    });
    bar.addEventListener('mousedown', (ev) => {
      // keep text editing alive while clicking props buttons
      if (ev.target.closest('button')) ev.preventDefault();
    });
    bar.addEventListener('click', (ev) => {
      const b = ev.target.closest('button');
      if (!b) return;
      if (b.dataset.act === 'del') return deleteSelected();
      if (b.dataset.act === 'dup') return duplicateSelected();
      if (b.dataset.act === 'front') {
        const a = activeObj();
        if (a) { a.o.bringToFront(); a.e.fc.requestRenderAll(); commit(a.e); }
        return;
      }
      if (b.dataset.p) {
        setProp(b.dataset.p, b.dataset.v, true);
        updateProps();
      }
    });
  }

  /* =================================================================
   * Object actions
   * ================================================================= */
  function deleteSelected() {
    const a = activeObj();
    if (!a) return;
    const objs = a.e.fc.getActiveObjects();
    a.e.fc.discardActiveObject();
    // deleting the replacement of an original text run deletes that text: keep an empty
    // box (and its cover, if any) so the original glyphs are still removed on export
    const keep = objs.filter((o) => o.kind === 'text' && o.srcItem != null);
    keep.forEach((o) => o.set('text', ''));
    const keepIds = new Set(keep.map((o) => o.srcItem));
    a.e.fc.remove(...objs.filter((o) => !keep.includes(o) && !(o.kind === 'whiteout' && keepIds.has(o.srcItem))));
    a.e.fc.requestRenderAll();
    commit(a.e);
    updateProps();
  }

  function cloneObj(o) {
    return new Promise((res) => o.clone(res, PROPS));
  }

  async function duplicateSelected() {
    const a = activeObj();
    if (!a || a.o.isEditing) return;
    const c = await cloneObj(a.o);
    pasteInto(a.e, c, 14);
  }

  function pasteInto(e, c, offset) {
    const fc = ensureFabric(e);
    fc.discardActiveObject();
    c.set({ left: c.left + offset, top: c.top + offset, evented: true });
    if (c.type === 'activeSelection') {
      c.canvas = fc;
      c.forEachObject((obj) => { obj.srcItem = undefined; fc.add(obj); });
      c.setCoords();
    } else {
      c.srcItem = undefined;
      fc.add(c);
    }
    fc.setActiveObject(c);
    fc.requestRenderAll();
    commit(e);
    updateProps();
  }

  async function copySelected() {
    const a = activeObj();
    if (!a || a.o.isEditing) return;
    E.clipboard = { obj: await cloneObj(a.o), from: a.e, n: 0 };
  }

  async function paste() {
    if (!E.clipboard) return;
    const target = E.current || E.order[0];
    if (!target) return;
    const c = await cloneObj(E.clipboard.obj);
    E.clipboard.n++;
    pasteInto(target, c, target === E.clipboard.from ? 14 * E.clipboard.n : 0);
  }

  function nudge(dx, dy) {
    const a = activeObj();
    if (!a) return;
    // arrow keys move in screen directions, also on user-rotated pages
    const { ux, uy } = screenDirs(a.e);
    a.o.set({ left: a.o.left + ux.x * dx + uy.x * dy, top: a.o.top + ux.y * dx + uy.y * dy });
    a.o.setCoords();
    a.e.fc.requestRenderAll();
    clearTimeout(E.nudgeT);
    E.nudgeT = setTimeout(() => commit(a.e), 300);
  }

  /* =================================================================
   * History
   * ================================================================= */
  function commit(e) {
    if (!e || !e.fc || e.restoring) return;
    const now = serialize(e);
    if (now === e.lastJSON) return;
    pushHistory({ type: 'canvas', e, before: e.lastJSON, after: now });
    e.lastJSON = now;
    refreshTextLayer(e);
  }
  function pushHistory(h) {
    E.history.push(h);
    if (E.history.length > 150) E.history.shift();
    E.future = [];
    E.dirty = true;
    updateDocDirty();
    updateUndo();
  }
  function updateUndo() {
    $('#undoBtn').disabled = !E.history.length;
    $('#redoBtn').disabled = !E.future.length;
  }
  function restoreCanvas(e, json) {
    return new Promise((res) => {
      e.restoring = true;
      e.fc.discardActiveObject();
      e.fc.loadFromJSON(hydrate(json), () => {
        e.fc.setViewportTransform(vpt(e));
        e.fc.renderAll();
        e.restoring = false;
        e.lastJSON = json;
        refreshTextLayer(e);
        res();
      });
    });
  }
  async function applyHist(h, which) {
    if (h.type === 'canvas') {
      await restoreCanvas(h.e, h[which]);
      if (E.order.includes(h.e) && !document.body.classList.contains('organize')) {
        const r = h.e.el.getBoundingClientRect(), vr = $('#pagesScroll').getBoundingClientRect();
        if (r.bottom < vr.top || r.top > vr.bottom) scrollToEntry(h.e);
      }
    } else {
      restorePages(h[which]);
    }
    E.dirty = true;
    updateProps();
    updateUndo();
  }
  function stopEditing() {
    const a = activeObj();
    if (a && a.o.isEditing) a.o.exitEditing();
  }
  async function undo() {
    stopEditing();
    const h = E.history.pop();
    if (!h) return;
    E.future.push(h);
    await applyHist(h, 'before');
  }
  async function redo() {
    stopEditing();
    const h = E.future.pop();
    if (!h) return;
    E.history.push(h);
    await applyHist(h, 'after');
  }

  /* =================================================================
   * Page operations
   * ================================================================= */
  function snapPages() {
    return E.order.map((e) => ({ e, rot: e.rot }));
  }
  function restorePages(snap) {
    const changedRot = [];
    E.order = snap.map((x) => {
      if (x.e.rot !== x.rot) { x.e.rot = x.rot; changedRot.push(x.e); }
      return x.e;
    });
    layout();
    changedRot.forEach(queueThumb);
  }
  function pageOp(fn) {
    stopEditing();
    const before = snapPages();
    const res = fn();
    if (res === false) return;
    pushHistory({ type: 'pages', before, after: snapPages() });
    layout();
  }

  function thumbAction(e, act) {
    const i = E.order.indexOf(e);
    if (act === 'rotl' || act === 'rotr') {
      pageOp(() => { e.rot = (e.rot + (act === 'rotr' ? 90 : 270)) % 360; });
      queueThumb(e);
    } else if (act === 'del') {
      if (E.order.length === 1) { toast('A PDF needs at least one page.'); return; }
      pageOp(() => { E.order.splice(i, 1); });
    } else if (act === 'dup') {
      const n = makeEntry({ srcId: e.srcId, pageIndex: e.pageIndex, page: e.page, blank: e.blank, baseRot: e.baseRot, W: e.W, H: e.H, T: e.T });
      n.rot = e.rot;
      // a page whose annotations are still loading is copied from the JSON being loaded
      n.pendingJSON = e.fc ? (e.loadingJSON || serialize(e)) : e.pendingJSON;
      pageOp(() => { E.order.splice(i + 1, 0, n); });
      queueThumb(n);
    } else if (act === 'blank') {
      const r = e.rot % 180 !== 0;
      const n = blankEntry(r ? e.H : e.W, r ? e.W : e.H);
      pageOp(() => { E.order.splice(i + 1, 0, n); });
      queueThumb(n);
    }
  }

  function addBlankAtEnd() {
    const last = E.order[E.order.length - 1];
    const r = last && last.rot % 180 !== 0;
    const n = last ? blankEntry(r ? last.H : last.W, r ? last.W : last.H) : blankEntry(595.28, 841.89);
    pageOp(() => { E.order.push(n); });
    queueThumb(n);
    if (!document.body.classList.contains('organize')) setTimeout(() => scrollToEntry(n), 50);
  }

  /* ---------- drag to reorder ---------- */
  let dragEntry = null;
  function bindThumbDnD(e) {
    const th = e.thumb;
    th.addEventListener('dragstart', (ev) => {
      dragEntry = e;
      th.classList.add('dragging');
      ev.dataTransfer.effectAllowed = 'move';
      try { ev.dataTransfer.setData('text/plain', String(e.id)); } catch (err) { /* noop */ }
    });
    th.addEventListener('dragend', () => {
      dragEntry = null;
      th.classList.remove('dragging');
      $$('.thumb.drop-before, .thumb.drop-after').forEach((x) => x.classList.remove('drop-before', 'drop-after'));
    });
    th.addEventListener('dragover', (ev) => {
      if (!dragEntry || dragEntry === e) return;
      ev.preventDefault();
      const r = th.getBoundingClientRect();
      const grid = document.body.classList.contains('organize');
      const after = grid ? ev.clientX > r.left + r.width / 2 : ev.clientY > r.top + r.height / 2;
      th.classList.toggle('drop-after', after);
      th.classList.toggle('drop-before', !after);
    });
    th.addEventListener('dragleave', () => th.classList.remove('drop-before', 'drop-after'));
    th.addEventListener('drop', (ev) => {
      ev.preventDefault();
      const after = th.classList.contains('drop-after');
      th.classList.remove('drop-before', 'drop-after');
      const moving = dragEntry;
      if (!moving || moving === e) return;
      pageOp(() => {
        E.order.splice(E.order.indexOf(moving), 1);
        E.order.splice(E.order.indexOf(e) + (after ? 1 : 0), 0, moving);
      });
    });
  }

  function setOrganize(on) {
    stopEditing();
    document.body.classList.toggle('organize', on);
    if (!on) {
      requestAnimationFrame(() => { scheduleRender(); if (E.current) scrollToEntry(E.current); });
    }
  }

  /* =================================================================
   * Zoom
   * ================================================================= */
  function setZoom(z) {
    z = Math.min(4, Math.max(0.25, z));
    const sc = $('#pagesScroll');
    const ratio = sc.scrollHeight ? (sc.scrollTop + sc.clientHeight / 2) / sc.scrollHeight : 0;
    E.zoom = z;
    E.order.forEach(sizeEntry);
    sc.scrollTop = ratio * sc.scrollHeight - sc.clientHeight / 2;
    $('#zoomVal').textContent = Math.round(z * 100) + '%';
    scheduleRender();
  }
  function fitWidth(initial) {
    const sc = $('#pagesScroll');
    const maxW = Math.max(...E.order.map((e) => (e.rot % 180 ? e.H : e.W)), 100);
    let z = (sc.clientWidth - 64) / maxW;
    if (initial) z = Math.min(z, 1.5);
    setZoom(Math.max(0.25, z));
    if (initial) sc.scrollTop = 0; // a newly opened document starts at its first page
  }

  /* =================================================================
   * Export
   * ================================================================= */
  function col(c) {
    if (!c || c === 'transparent') return null;
    const s = new fabric.Color(c).getSource();
    if (!s || s[3] === 0) return null;
    return PDFLib.rgb(s[0] / 255, s[1] / 255, s[2] / 255);
  }

  const FONT_MAP = {
    Helvetica: ['Helvetica', 'HelveticaBold', 'HelveticaOblique', 'HelveticaBoldOblique'],
    Times: ['TimesRoman', 'TimesRomanBold', 'TimesRomanItalic', 'TimesRomanBoldItalic'],
    Courier: ['Courier', 'CourierBold', 'CourierOblique', 'CourierBoldOblique'],
  };
  async function getFont(ctx, o) {
    const set = FONT_MAP[o.pdfFont] || FONT_MAP.Helvetica;
    const idx = (o.fontWeight === 'bold' || +o.fontWeight >= 600 ? 1 : 0) + (o.fontStyle === 'italic' ? 2 : 0);
    const name = set[idx];
    if (!ctx.fonts.has(name)) ctx.fonts.set(name, await ctx.doc.embedFont(PDFLib.StandardFonts[name]));
    return ctx.fonts.get(name);
  }
  function sanitize(ctx, font, s) {
    let out = '';
    for (const ch of s.replace(/\t/g, '    ')) {
      const key = font.name + '|' + ch;
      let ok = ctx.charOk.get(key);
      if (ok === undefined) {
        try { font.encodeText(ch); ok = true; } catch (e) { ok = false; }
        ctx.charOk.set(key, ok);
      }
      if (ok) out += ch;
      else { out += '?'; ctx.replaced++; }
    }
    return out;
  }
  async function embedImage(ctx, src) {
    if (ctx.images.has(src)) return ctx.images.get(src);
    let url = src;
    if (!/^data:image\/(png|jpeg)/.test(url)) {
      const img = await UI.loadImage(src);
      const c = document.createElement('canvas');
      c.width = img.naturalWidth; c.height = img.naturalHeight;
      c.getContext('2d').drawImage(img, 0, 0);
      url = c.toDataURL('image/png');
    }
    const bytes = await (await fetch(url)).arrayBuffer();
    const img = /^data:image\/png/.test(url) ? await ctx.doc.embedPng(bytes) : await ctx.doc.embedJpg(bytes);
    ctx.images.set(src, img);
    return img;
  }
  function pathToSvg(o) {
    const ox = o.pathOffset.x, oy = o.pathOffset.y;
    return o.path.map((seg) => {
      const [cmd, ...n] = seg;
      const pts = [];
      for (let i = 0; i + 1 < n.length; i += 2) pts.push((n[i] - ox).toFixed(2), (n[i + 1] - oy).toFixed(2));
      return cmd + ' ' + pts.join(' ');
    }).join(' ');
  }

  async function drawObject(ctx, page, o) {
    const { LineCapStyle } = PDFLib;
    const op = o.opacity == null ? 1 : o.opacity;
    if (o.type === 'textbox' || o.type === 'i-text' || o.type === 'text') {
      const font = await getFont(ctx, o);
      const size = o.fontSize;
      const color = col(o.fill) || PDFLib.rgb(0, 0, 0);
      const top = -o.height / 2;
      let acc = 0;
      o.textLines.forEach((line, i) => {
        const lh = o.getHeightOfLine(i);
        const maxH = lh / o.lineHeight;
        const baseline = top + acc + maxH * (1 - o._fontSizeFraction);
        acc += lh;
        const txt = sanitize(ctx, font, line);
        if (!txt.trim()) return;
        const tw = font.widthOfTextAtSize(txt, size);
        let x = -o.width / 2;
        if (o.textAlign === 'center') x = -tw / 2;
        else if (o.textAlign === 'right') x = o.width / 2 - tw;
        page.drawText(txt, { x, y: -baseline, size, font, color, opacity: op });
      });
    } else if (o.type === 'image') {
      const img = await embedImage(ctx, o.getSrc());
      page.drawImage(img, { x: -o.width / 2, y: -o.height / 2, width: o.width, height: o.height, opacity: op });
    } else if (o.type === 'rect' || o.type === 'ellipse') {
      const opts = { opacity: op, borderOpacity: op };
      const f = col(o.fill), s = col(o.stroke);
      if (f) opts.color = f;
      if (s && o.strokeWidth > 0) { opts.borderColor = s; opts.borderWidth = o.strokeWidth; }
      if (!opts.color && !opts.borderColor) return;
      if (o.type === 'rect') page.drawRectangle({ x: -o.width / 2, y: -o.height / 2, width: o.width, height: o.height, ...opts });
      else page.drawEllipse({ x: 0, y: 0, xScale: o.rx, yScale: o.ry, ...opts });
    } else if (o.type === 'line') {
      const p = o.calcLinePoints();
      const sc = o.strokeUniform ? Math.sqrt(Math.abs(o.scaleX * o.scaleY)) || 1 : 1;
      page.drawLine({
        start: { x: p.x1, y: -p.y1 }, end: { x: p.x2, y: -p.y2 },
        thickness: o.strokeWidth / sc, color: col(o.stroke) || PDFLib.rgb(0, 0, 0), opacity: op, lineCap: LineCapStyle.Round,
      });
    } else if (o.type === 'path') {
      const c = new fabric.Color(o.stroke || '#000');
      const alpha = c.getAlpha();
      if (o.strokeLineJoin === 'round' || o.strokeLineJoin == null) page.pushOperators(PDFLib.setLineJoin(PDFLib.LineJoinStyle.Round));
      else if (o.strokeLineJoin === 'bevel') page.pushOperators(PDFLib.setLineJoin(PDFLib.LineJoinStyle.Bevel));
      page.drawSvgPath(pathToSvg(o), {
        x: 0, y: 0, borderColor: col(o.stroke) || PDFLib.rgb(0, 0, 0), borderWidth: o.strokeWidth,
        borderOpacity: op * alpha, borderLineCap: LineCapStyle.Round,
      });
    }
  }

  /**
   * Plan in-place text edits for a page: which original glyphs to remove from the content
   * stream, and how each replacement textbox is drawn (original font, or standard-font fallback).
   */
  async function textPlan(e) {
    const plan = { remove: [], inserts: [], objs: new Map(), an: null };
    if (e.blank || !e.fc) return plan;
    const objs = textObjs(e);
    if (!objs.length) return plan;
    await loadTextItems(e);
    const an = (plan.an = await pageAnalysis(e));
    const info = [];
    for (const o of objs) {
      const ti = e.textItems[o.srcItem];
      if (!ti) continue;
      const m = await editInfo(e, ti);
      const init = initStyle(e, ti, m);
      const moved = Math.abs(o.left - init.left) > 1e-3 || Math.abs(o.top - init.top) > 1e-3;
      const plain = (o.angle || 0) === 0 && o.scaleX === 1 && o.scaleY === 1 && !o.flipX && !o.flipY
        && !o.skewX && !o.skewY && (o.opacity == null || o.opacity === 1);
      const sameStyle = plain && o.fontFamily === init.fontFamily && Math.abs(o.fontSize - init.fontSize) < 1e-3
        && o.fontWeight === init.fontWeight && o.fontStyle === init.fontStyle
        && !(o.styles && Object.keys(o.styles).length);
      const sameFill = toHex(o.fill) === toHex(init.fill);
      const unchanged = o.text === ti.str && !moved && sameStyle && sameFill && (o.textAlign || 'left') === 'left';
      if (!m || !m.ok) {
        // cover-box fallback: a run left exactly as it was keeps its original glyphs - neither
        // the cover nor the standard-font redraw is exported
        if (unchanged) {
          plan.objs.set(o, { skip: true });
          e.fc.getObjects().forEach((w) => { if (w.kind === 'whiteout' && w.srcItem === o.srcItem) plan.objs.set(w, { skip: true }); });
        }
        continue;
      }
      info.push({ o, ti, m, init, sameStyle, sameFill, unchanged });
    }
    // a run is removed if any of its textboxes changed it; unchanged ones are then no-ops
    const removeRuns = new Set(info.filter((x) => !x.unchanged).map((x) => x.ti.gi));
    const perRun = new Map();
    info.forEach((x) => perRun.set(x.ti.gi, (perRun.get(x.ti.gi) || 0) + 1));
    const seen = new Set();
    for (const x of info) {
      if (!removeRuns.has(x.ti.gi)) { plan.objs.set(x.o, { skip: true }); continue; }
      // single unmoved line, same style & colour: touch only the glyphs that changed
      if (x.m.native && x.sameStyle && x.sameFill && perRun.get(x.ti.gi) === 1 && x.o.textLines.length === 1
        && (x.o.textAlign || 'left') === 'left' && Math.abs(x.o.left - x.init.left) < 1e-3 && Math.abs(x.o.top - x.init.top) < 1e-3) {
        // only worth it when the run mixes text states; otherwise the full (prefix/suffix
        // preserving) redraw is pixel-identical and keeps the run as one string for extraction
        const g0 = x.m.glyphs[0].st;
        const mixed = x.m.glyphs.some((g) => g.st !== g0 && JSON.stringify([g.st.Tc, g.st.Tw, g.st.Th, g.st.Ts, g.st.Tr, g.st.fill])
          !== JSON.stringify([g0.Tc, g0.Tw, g0.Th, g0.Ts, g0.Tr, g0.fill]));
        const mini = mixed ? TextEdit.minimalEdit(an, x.m, x.o.textLines[0]) : null;
        if (mini && !mini.missing) {
          const ref = mini.m2;
          const anchor = ref ? x.m.glyphs.find((g) => g.Tm === ref.Tm0).op : -1;
          const txt = ref ? TextEdit.inlineOps(an, anchor, ref, [{ items: mini.items, tm: ref.Tm0 }]) : '';
          if (txt !== null) {
            plan.remove.push(...mini.remove);
            if (txt) plan.inserts.push({ op: anchor, text: txt });
            plan.objs.set(x.o, { skip: true });
            continue;
          }
          plan.remove.push(...mini.remove);
          plan.objs.set(x.o, { minimal: mini });
          continue;
        }
      }
      if (!seen.has(x.ti.gi)) { seen.add(x.ti.gi); plan.remove.push(...x.m.glyphs); }
      let native = null;
      if (x.sameStyle && x.m.native) {
        const { lines, missing } = nativeLines(an, x.m, x.o);
        if (!missing.length) native = lines;
        else plan.fallbackChars = (plan.fallbackChars || []).concat(missing);
      }
      if (native) {
        // draw inside the original text object, right where the run was (reading order, clip, z-order)
        const anchor = Math.min(...x.m.glyphs.map((g) => g.op));
        let rgb = null;
        if (!x.sameFill) {
          const c = new fabric.Color(x.o.fill || '#000').getSource() || [0, 0, 0];
          rgb = [c[0] / 255, c[1] / 255, c[2] / 255];
        }
        const lines = nativeGeometry(e, x.o, x.m, native).map((l) => ({ items: l.items, tm: TextEdit.lineTm(x.m, [l.dx, l.dy]) }));
        const txt = TextEdit.inlineOps(an, anchor, x.m, lines, { rgb });
        if (txt !== null) {
          if (txt) plan.inserts.push({ op: anchor, text: txt });
          plan.objs.set(x.o, { skip: true });
          continue;
        }
      }
      plan.objs.set(x.o, { native, x });
    }
    return plan;
  }

  /** Draw a replacement textbox with the original font resource of the run it replaces. */
  /** Per-line user-space offsets of a textbox's lines relative to the original run origin. */
  function nativeGeometry(e, o, m, native) {
    let acc = 0;
    return native.map((ln, i) => {
      const lh = o.getHeightOfLine(i);
      const baseline = o.top + acc + (lh / o.lineHeight) * (1 - o._fontSizeFraction);
      acc += lh;
      const wVp = ln.width * m.unitVp;
      let x = o.left;
      if (o.textAlign === 'center') x += (o.width - wVp) / 2;
      else if (o.textAlign === 'right') x += o.width - wVp;
      const [dx, dy] = TextEdit.vpDeltaToUser(e.T, x - m.originVp[0], baseline - m.originVp[1]);
      return { items: ln.items, dx, dy };
    });
  }

  function drawNativeText(ctx, page, e, o, p) {
    const { m } = p.x;
    const lines = nativeGeometry(e, o, m, p.native);
    let rgb = null;
    if (!p.x.sameFill) {
      const s = new fabric.Color(o.fill || '#000').getSource() || [0, 0, 0];
      rgb = [s[0] / 255, s[1] / 255, s[2] / 255];
    }
    const ops = TextEdit.drawOps(ctx.doc, p.an, m, lines, { rgb });
    if (ops.length) page.pushOperators(...ops);
  }

  async function drawObjects(ctx, page, e, plan) {
    const { pushGraphicsState, popGraphicsState, concatTransformationMatrix } = PDFLib;
    const invT = inv(e.T);
    for (const o of e.fc.getObjects()) {
      const p = plan && plan.objs.get(o);
      if (p && p.skip) continue;
      if (p && p.minimal) {
        if (p.minimal.m2) {
          const ops = TextEdit.drawOps(ctx.doc, plan.an, p.minimal.m2, [{ items: p.minimal.items, dx: 0, dy: 0 }]);
          if (ops.length) page.pushOperators(...ops);
        }
        continue;
      }
      if (p && p.native) { drawNativeText(ctx, page, e, o, Object.assign({ an: plan.an }, p)); continue; }
      let src = o;
      if (p && p.x && p.x.init.face) {
        // fallback for an embedded-face textbox: closest standard font with the original weight/style
        src = Object.create(o, {
          fontWeight: { value: o.fontWeight === 'bold' ? 'bold' : p.x.init.guess.fontWeight },
          fontStyle: { value: o.fontStyle === 'italic' ? 'italic' : p.x.init.guess.fontStyle },
        });
      }
      const m = mul(mul([1, 0, 0, -1, 0, 0], o.calcTransformMatrix()), invT);
      page.pushOperators(pushGraphicsState(), concatTransformationMatrix(...m));
      try {
        await drawObject(ctx, page, src);
      } finally {
        page.pushOperators(popGraphicsState());
      }
    }
  }

  /** Give each leaf its inherited Resources/MediaBox/CropBox/Rotate before the tree is rebuilt. */
  function inheritAttrs(doc, pages) {
    const { PDFName, PDFDict } = PDFLib;
    const keys = ['Resources', 'MediaBox', 'CropBox', 'Rotate'].map((k) => PDFName.of(k));
    for (const p of pages) {
      for (const n of keys) {
        if (p.node.get(n)) continue;
        const v = p.node.getInheritableAttribute(n);
        if (v) p.node.set(n, v instanceof PDFDict ? v.clone(doc.context) : v);
      }
    }
  }

  /** Give a page its own /Contents array (pdf-lib appends to it in place; it may be shared). */
  function ownContents(doc, page) {
    const { PDFName, PDFArray, PDFRef } = PDFLib;
    const n = PDFName.of('Contents');
    let c = page.node.get(n);
    if (c instanceof PDFRef) c = doc.context.lookup(c);
    if (c instanceof PDFArray) page.node.set(n, doc.context.obj(c.asArray().slice()));
  }

  /**
   * Drop every object not reachable from the trailer. Pages that are no longer in the page tree
   * are never followed (links, widget /P, outlines may still point at them), so deleted pages'
   * content, images and fonts don't stay recoverable inside the exported file.
   */
  function pruneUnreachable(doc, keepRefs) {
    const { PDFRef, PDFDict, PDFArray, PDFStream, PDFName } = PDFLib;
    const cx = doc.context;
    const keep = new Set(keepRefs.map((r) => r.toString()));
    const TypeN = PDFName.of('Type'), PageN = PDFName.of('Page');
    const seen = new Set();
    const t = cx.trailerInfo;
    const stack = [t.Root, t.Info, t.Encrypt, t.ID].filter(Boolean);
    while (stack.length) {
      const o = stack.pop();
      if (o instanceof PDFRef) {
        const k = o.toString();
        if (seen.has(k)) continue;
        const v = cx.lookup(o);
        if (!v) continue;
        if (v instanceof PDFDict && v.get(TypeN) === PageN && !keep.has(k)) continue;
        seen.add(k);
        stack.push(v);
      } else if (o instanceof PDFStream) {
        stack.push(o.dict);
      } else if (o instanceof PDFDict) {
        for (const [, v] of o.entries()) stack.push(v);
      } else if (o instanceof PDFArray) {
        for (const v of o.asArray()) stack.push(v);
      }
    }
    let n = 0;
    for (const [ref] of cx.enumerateIndirectObjects()) if (!seen.has(ref.toString())) { cx.delete(ref); n++; }
    return n;
  }

  /** Base-viewport rectangles of annotations that viewers paint above page content. */
  async function annotRects(e) {
    try {
      const page = await srcPdfPage(e);
      const list = await page.getAnnotations();
      return list
        .filter((a) => a.rect && !['Link', 'Popup'].includes(a.subtype) && !a.hidden && !a.noView)
        .map((a) => {
          const p = pdfjsLib.Util.applyTransform([a.rect[0], a.rect[1]], e.T);
          const q = pdfjsLib.Util.applyTransform([a.rect[2], a.rect[3]], e.T);
          return { x0: Math.min(p[0], q[0]), y0: Math.min(p[1], q[1]), x1: Math.max(p[0], q[0]), y1: Math.max(p[1], q[1]) };
        });
    } catch (err) {
      return [];
    }
  }

  async function buildPdf() {
    const { PDFDocument, degrees } = PDFLib;
    E.order.forEach((e) => {
      if (!e.fc) return;
      const a = e.fc.getActiveObject();
      if (a && a.isEditing) a.exitEditing();
      e.fc.discardActiveObject();
      e.fc.requestRenderAll();
    });
    // pages that were never displayed but carry duplicated annotations: wait until every object
    // (images and signatures decode asynchronously) is really on the canvas
    E.order.forEach((e) => { if (e.pendingJSON) ensureFabric(e); });
    await Promise.all(E.order.map((e) => e.ready).filter(Boolean));

    // base document (keeps outline, forms, metadata...): the source with the most pages in the
    // output, ties going to the first opened file - not whichever page happens to be first
    const counts = new Map();
    E.order.forEach((e) => { if (!e.blank) counts.set(e.srcId, (counts.get(e.srcId) || 0) + 1); });
    let baseId = null;
    [...counts.keys()].sort((a, b) => a - b).forEach((id) => { if (baseId == null || counts.get(id) > counts.get(baseId)) baseId = id; });
    let doc, basePages = [];
    if (baseId != null) {
      doc = await PDFDocument.load(srcOf(baseId).bytes, { updateMetadata: false });
      basePages = doc.getPages();
      inheritAttrs(doc, basePages);
      for (let i = doc.getPageCount() - 1; i >= 0; i--) doc.removePage(i);
    } else {
      doc = await PDFDocument.create();
    }
    // every other page is copied with ONE copyPages call per source (and per repeat of a
    // duplicated page), so resources the pages share are copied once, not once per page
    const used = new Set();
    const slots = [];
    const need = new Map(); // srcId -> [[pageIndex...] per batch]
    for (const e of E.order) {
      if (e.blank) { slots.push({ e }); continue; }
      if (e.srcId === baseId && !used.has(e.pageIndex)) { used.add(e.pageIndex); slots.push({ e, page: basePages[e.pageIndex] }); continue; }
      if (!need.has(e.srcId)) need.set(e.srcId, []);
      const batches = need.get(e.srcId);
      let b = batches.findIndex((list) => !list.includes(e.pageIndex));
      if (b < 0) { batches.push([]); b = batches.length - 1; }
      slots.push({ e, src: e.srcId, b, k: batches[b].length });
      batches[b].push(e.pageIndex);
    }
    const copied = new Map();
    for (const [id, batches] of need) {
      const src = await PDFDocument.load(srcOf(id).bytes, { updateMetadata: false });
      const out = [];
      for (const list of batches) out.push(await doc.copyPages(src, list));
      copied.set(id, out);
    }
    const ctx = { doc, fonts: new Map(), images: new Map(), charOk: new Map(), replaced: 0, fontFallback: new Set() };
    const keep = [];
    const coveredAnnots = [];
    for (let n = 0; n < slots.length; n++) {
      const sl = slots[n], e = sl.e;
      let page;
      if (e.blank) page = doc.addPage([e.W, e.H]);
      else if (sl.page) page = doc.addPage(sl.page);
      else page = doc.addPage(copied.get(sl.src)[sl.b][sl.k]);
      ownContents(doc, page);
      keep.push(page.ref);
      page.setRotation(degrees((e.baseRot + e.rot) % 360));
      // in-place text edits: take exactly the replaced glyphs out of the content stream
      const plan = await textPlan(e);
      if (plan.remove.length || plan.inserts.length) TextEdit.setContent(doc, page, TextEdit.rewrite(plan.an, plan.remove, plan.inserts));
      if (plan.fallbackChars) plan.fallbackChars.forEach((c) => ctx.fontFallback.add(c));
      if (e.fc && e.fc.getObjects().length) {
        await drawObjects(ctx, page, e, plan);
        // annotations / form fields are painted above page content by every viewer, so a cover
        // drawn over one on screen would not hide it in the file - tell the user
        const covers = e.fc.getObjects().filter((o) => !(plan.objs.get(o) || {}).skip
          && (o.kind === 'whiteout' || ((o.type === 'rect' || o.type === 'ellipse') && col(o.fill) && (o.opacity == null || o.opacity >= 0.5))));
        if (covers.length && !e.blank) {
          const ar = await annotRects(e);
          const hit = covers.some((o) => {
            const r = o.getBoundingRect(true, true);
            return ar.some((a) => r.left < a.x1 && r.left + r.width > a.x0 && r.top < a.y1 && r.top + r.height > a.y0);
          });
          if (hit) coveredAnnots.push(n + 1);
        }
      }
    }
    doc.setProducer('Pagecraft');
    doc.setModificationDate(new Date());
    await doc.flush();
    pruneUnreachable(doc, keep);
    const bytes = await doc.save();
    if (ctx.fontFallback.size) {
      toast(`The original font doesn't contain “${[...ctx.fontFallback].join(' ')}”, so the edited text using them was saved in a standard font.`, 'error', 8000);
    }
    if (coveredAnnots.length) {
      toast(`On page ${coveredAnnots.join(', ')}, a cover overlaps a form field or annotation. PDF viewers draw those on top of the page, so they will still be visible in the saved file.`, 'error', 9000);
    }
    return { bytes, replaced: ctx.replaced, fontFallback: [...ctx.fontFallback], coveredAnnots };
  }

  async function exportPdf() {
    if (!E.order.length) return;
    busy('Applying changes…');
    try {
      const { bytes, replaced } = await buildPdf();
      downloadBlob(bytes, baseName(E.fileName) + (E.sources.size > 1 ? '' : '-edited') + '.pdf');
      E.dirty = false;
      toast('Your PDF is ready — download started.', 'ok');
      if (replaced) toast(`${replaced} character(s) aren't supported by the standard PDF fonts and were replaced with “?”.`, 'error', 8000);
    } catch (err) {
      console.error(err);
      toast('Could not create the PDF: ' + (err.message || err), 'error');
    } finally {
      busy(false);
    }
  }

  /* =================================================================
   * Wiring
   * ================================================================= */
  function init() {
    $('#toolbar').addEventListener('click', (ev) => {
      const b = ev.target.closest('.tool');
      if (!b) return;
      if (b.dataset.tool === 'shapes') {
        ev.stopPropagation();
        const menu = $('#shapesMenu');
        menu.hidden = !menu.hidden;
        if (!menu.hidden) {
          // used by the small-screen layout, where the menu is position:fixed
          const r = b.getBoundingClientRect();
          const left = Math.max(8, Math.min(r.left, window.innerWidth - 168));
          menu.style.setProperty('--menu-top', Math.round(r.bottom + 6) + 'px');
          menu.style.setProperty('--menu-left', Math.round(left) + 'px');
        }
        return;
      }
      setTool(b.dataset.tool);
    });
    // the menu is fixed-positioned on small screens: don't leave it behind when the toolbar scrolls
    $('#toolbar').addEventListener('scroll', () => { $('#shapesMenu').hidden = true; }, { passive: true });
    $('#shapesMenu').addEventListener('click', (ev) => {
      const b = ev.target.closest('button[data-shape]');
      if (!b) return;
      E.lastShape = b.dataset.shape;
      $('#shapesMenu').hidden = true;
      setTool(b.dataset.shape);
    });
    document.addEventListener('click', (ev) => {
      if (!ev.target.closest('.tool-menu-wrap')) $('#shapesMenu').hidden = true;
    });

    $('#imageInput').addEventListener('change', async (ev) => {
      const f = ev.target.files[0];
      if (!f) return;
      try { placeImage(await imageFileToDataURL(f), 'image'); } catch (err) { toast('Could not read that image.', 'error'); }
    });

    $('#undoBtn').addEventListener('click', undo);
    $('#redoBtn').addEventListener('click', redo);
    $('#zoomIn').addEventListener('click', () => setZoom(E.zoom * 1.2));
    $('#zoomOut').addEventListener('click', () => setZoom(E.zoom / 1.2));
    $('#zoomVal').addEventListener('click', () => fitWidth(false));
    $('#exportBtn').addEventListener('click', exportPdf);
    // ---- multiple documents ----
    $('#docPrev').addEventListener('click', prevDoc);
    $('#docNext').addEventListener('click', nextDoc);
    $('#zipBtn').addEventListener('click', downloadAll);
    $('#docAdd').addEventListener('click', () => {
      const inp = $('#pdfMultiInput');
      inp.value = '';
      inp.onchange = () => addDocs(inp.files);
      inp.click();
    });
    $('#docTabs').addEventListener('click', (ev) => {
      const tab = ev.target.closest('.doc-tab');
      if (!tab) return;
      const i = +tab.dataset.i;
      if (ev.target.closest('[data-close]')) { closeDoc(i); return; }
      activate(i, i > E.active ? 'next' : 'prev');
    });
    // swipe left/right on the page area (touch) to move between documents
    {
      const sc = $('#pagesScroll');
      let sw = null;
      const selKey = () => { const a = activeObj(); return a ? `${a.o.left},${a.o.top},${a.o.scaleX}` : ''; };
      sc.addEventListener('touchstart', (ev) => {
        sw = E.docs.length > 1 && ev.touches.length === 1
          ? { x: ev.touches[0].clientX, y: ev.touches[0].clientY, t: performance.now(), sl: sc.scrollLeft, sel: selKey() }
          : null;
      }, { passive: true });
      sc.addEventListener('touchmove', (ev) => { if (sw && ev.touches.length > 1) sw = null; }, { passive: true });
      sc.addEventListener('touchend', (ev) => {
        const s0 = sw;
        sw = null;
        if (!s0 || !['select', 'edittext'].includes(E.tool)) return;
        const t = ev.changedTouches[0];
        const dx = t.clientX - s0.x, dy = t.clientY - s0.y;
        if (performance.now() - s0.t > 700 || Math.abs(dx) < 70 || Math.abs(dy) > Math.abs(dx) * 0.6) return;
        if (Math.abs(sc.scrollLeft - s0.sl) > 2) return; // it scrolled a zoomed-in page instead
        if (selKey() !== s0.sel) return; // it moved an object
        const a = activeObj();
        if (a && a.o.isEditing) return;
        dx < 0 ? nextDoc() : prevDoc();
      }, { passive: true });
      // two-finger horizontal swipe on a trackpad
      let acc = 0, accT = 0, cool = 0;
      sc.addEventListener('wheel', (ev) => {
        if (E.docs.length < 2 || ev.ctrlKey || Math.abs(ev.deltaX) <= Math.abs(ev.deltaY)) return;
        if (sc.scrollWidth > sc.clientWidth + 1) return; // horizontal scrolling of a wide page wins
        const now = performance.now();
        if (now < cool) return;
        if (now - accT > 250) acc = 0;
        accT = now;
        acc += ev.deltaX;
        if (Math.abs(acc) > 160) {
          cool = now + 700;
          const fwd = acc > 0;
          acc = 0;
          fwd ? nextDoc() : prevDoc();
        }
      }, { passive: true });
    }
    $('#gridBtn').addEventListener('click', () => setOrganize(!document.body.classList.contains('organize')));
    $('#gridDone').addEventListener('click', () => setOrganize(false));
    $('#addBlankBtn').addEventListener('click', addBlankAtEnd);
    $('#addPdfBtn').addEventListener('click', () => {
      const inp = $('#pdfMultiInput');
      inp.value = '';
      inp.onchange = () => addFiles(inp.files);
      inp.click();
    });
    $('#sidebarToggle').addEventListener('click', () => document.body.classList.toggle('sidebar-open'));
    $('#pagesScroll').addEventListener('scroll', scheduleRender, { passive: true });
    $('#pagesScroll').addEventListener('pointerdown', (ev) => {
      document.body.classList.remove('sidebar-open');
      // click on the gray background clears selection
      if (ev.target === ev.currentTarget || ev.target.id === 'pagesContainer') {
        E.order.forEach((e) => { if (e.fc && e.fc.getActiveObject()) { stopEditing(); e.fc.discardActiveObject(); e.fc.requestRenderAll(); } });
        updateProps();
      }
    });
    $('#pagesScroll').addEventListener('wheel', (ev) => {
      if (!ev.ctrlKey) return;
      ev.preventDefault();
      setZoom(E.zoom * (ev.deltaY < 0 ? 1.1 : 1 / 1.1));
    }, { passive: false });
    window.addEventListener('resize', scheduleRender);
    bindProps();

    // drop PDFs onto the editor to merge
    const main = $('#view-editor');
    main.addEventListener('dragover', (ev) => { if (ev.dataTransfer.types.includes('Files')) ev.preventDefault(); });
    main.addEventListener('drop', async (ev) => {
      if (!ev.dataTransfer.files.length) return;
      ev.preventDefault();
      const all = Array.from(ev.dataTransfer.files);
      const pdfs = UI.filterPdfs ? await UI.filterPdfs(all) : all.filter(isPdf);
      if (pdfs.length) (E.docs.length > 1 ? addDocs(pdfs) : addFiles(pdfs));
      else {
        const img = all.find((f) => f.type.startsWith('image/'));
        if (img) imageFileToDataURL(img).then((u) => placeImage(u, 'image'));
      }
    });

    document.addEventListener('keydown', (ev) => {
      if (document.body.dataset.view !== 'editor' || !$('#signModal').hidden) return;
      const t = ev.target;
      const inField = t.tagName === 'TEXTAREA' || t.tagName === 'SELECT' || (t.tagName === 'INPUT' && !['range', 'checkbox', 'color'].includes(t.type)) || t.isContentEditable;
      const mod = ev.metaKey || ev.ctrlKey;
      const k = ev.key.toLowerCase();
      if (inField) {
        if (k === 'escape') stopEditing();
        return;
      }
      if (ev.altKey && !mod && (k === 'arrowleft' || k === 'arrowright') && E.docs.length > 1) {
        ev.preventDefault();
        k === 'arrowright' ? nextDoc() : prevDoc();
        return;
      }
      if (mod && k === 'z') { ev.preventDefault(); ev.shiftKey ? redo() : undo(); return; }
      if (mod && k === 'y') { ev.preventDefault(); redo(); return; }
      if (mod && k === 'c') { copySelected(); return; }
      if (mod && k === 'v') { ev.preventDefault(); paste(); return; }
      if (mod && k === 'd') { ev.preventDefault(); duplicateSelected(); return; }
      if (mod && (k === '=' || k === '+')) { ev.preventDefault(); setZoom(E.zoom * 1.2); return; }
      if (mod && k === '-') { ev.preventDefault(); setZoom(E.zoom / 1.2); return; }
      if (mod) return;
      const organizing = document.body.classList.contains('organize');
      if (k === 'delete' || k === 'backspace') { if (!organizing && activeObj()) { ev.preventDefault(); deleteSelected(); } return; }
      if (k === 'escape') {
        E.order.forEach((e) => { if (e.fc) { e.fc.discardActiveObject(); e.fc.requestRenderAll(); } });
        setTool('select');
        return;
      }
      const arrows = { arrowleft: [-1, 0], arrowright: [1, 0], arrowup: [0, -1], arrowdown: [0, 1] };
      if (arrows[k] && !organizing && activeObj()) {
        ev.preventDefault();
        const s = ev.shiftKey ? 10 : 1;
        nudge(arrows[k][0] * s, arrows[k][1] * s);
        return;
      }
      const shortcuts = { v: 'select', t: 'text', e: 'edittext', d: 'draw', h: 'highlight', w: 'whiteout' };
      if (shortcuts[k]) setTool(shortcuts[k]);
    });

    window.addEventListener('beforeunload', (ev) => {
      if (document.body.dataset.view === 'editor' && hasChanges()) { ev.preventDefault(); ev.returnValue = ''; }
    });
  }

  /** Unsaved work: committed changes, or a textbox still being typed into. */
  function hasChanges() {
    if (E.dirty) return true;
    if (E.docs.some((d, i) => i !== E.active && d.dirty)) return true;
    return E.order.some((e) => {
      const a = e.fc && e.fc.getActiveObject();
      return !!(a && a.isEditing && a.text !== a._textBeforeEdit);
    });
  }

  init();

  window.Editor = {
    open,
    openBlank: () => open([], { blank: true }),
    addDocs,
    downloadAll,
    hasChanges,
    close: () => reset(),
    buildPdf,
    _state: E,
  };
})();
