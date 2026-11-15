/* Signature modal: draw / type / upload / saved. Resolves with a PNG data URL or null. */
(function () {
  'use strict';
  const { $, $$, el, icon, toast, imageFileToDataURL, store } = UI;
  const STORE_KEY = 'pagecraft.signatures';

  let resolver = null;
  let tab = 'draw';
  let color = '#111827';
  let font = 'Dancing Script';
  let strokes = [];
  let current = null;
  let uploaded = null;
  let savedPick = null;
  let activeId = null;
  let prevFocus = null;
  let inerted = [];
  let downOnBackdrop = false;
  const REMEMBER_KEY = 'pagecraft.rememberSig';

  const modal = $('#signModal');
  const pad = $('#sigPad');
  const ctx = pad.getContext('2d');

  /* ---------- drawing pad ---------- */
  function sizePad() {
    const r = pad.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    pad.width = Math.round(r.width * dpr);
    pad.height = Math.round(r.height * dpr);
    redraw();
  }

  function drawStroke(c, s, scale) {
    const p = s.points;
    if (!p.length) return;
    c.strokeStyle = s.color;
    c.lineWidth = 2.6 * scale;
    c.lineCap = 'round';
    c.lineJoin = 'round';
    c.beginPath();
    c.moveTo(p[0].x * scale, p[0].y * scale);
    if (p.length === 1) c.lineTo(p[0].x * scale + 0.1, p[0].y * scale);
    for (let i = 1; i < p.length - 1; i++) {
      const mx = (p[i].x + p[i + 1].x) / 2;
      const my = (p[i].y + p[i + 1].y) / 2;
      c.quadraticCurveTo(p[i].x * scale, p[i].y * scale, mx * scale, my * scale);
    }
    if (p.length > 1) c.lineTo(p[p.length - 1].x * scale, p[p.length - 1].y * scale);
    c.stroke();
  }

  function redraw() {
    const dpr = window.devicePixelRatio || 1;
    ctx.clearRect(0, 0, pad.width, pad.height);
    strokes.forEach((s) => drawStroke(ctx, s, dpr));
  }

  function pos(e) {
    const r = pad.getBoundingClientRect();
    return { x: e.clientX - r.left, y: e.clientY - r.top };
  }

  pad.addEventListener('pointerdown', (e) => {
    // One stroke at a time: ignore secondary buttons, extra fingers and palm contacts.
    if (e.button !== 0 || current) return;
    if (e.pointerType === 'touch' && !e.isPrimary) return;
    activeId = e.pointerId;
    pad.setPointerCapture(e.pointerId);
    current = { color, points: [pos(e)] };
    strokes.push(current);
    redraw();
  });
  pad.addEventListener('pointermove', (e) => {
    if (!current || e.pointerId !== activeId) return;
    current.points.push(pos(e));
    redraw();
  });
  const end = (e) => {
    if (e.pointerId !== activeId) return;
    current = null;
    activeId = null;
  };
  pad.addEventListener('pointerup', end);
  pad.addEventListener('pointercancel', end);

  $('#sigClear').addEventListener('click', () => { strokes = []; redraw(); });
  $('#sigColors').addEventListener('click', (e) => {
    const b = e.target.closest('.sw');
    if (!b) return;
    color = b.dataset.c;
    $$('#sigColors .sw').forEach((x) => x.classList.toggle('on', x === b));
    strokes.forEach((s) => { s.color = color; });
    redraw();
    updateTypePreview();
  });

  /* ---------- type ---------- */
  function updateTypePreview() {
    const name = $('#sigName').value.trim() || 'Your Name';
    $$('#sigFonts button').forEach((b) => { b.textContent = name; b.style.color = color; });
  }
  $('#sigName').addEventListener('input', updateTypePreview);
  $('#sigFonts').addEventListener('click', (e) => {
    const b = e.target.closest('button');
    if (!b) return;
    font = b.dataset.font;
    $$('#sigFonts button').forEach((x) => x.classList.toggle('on', x === b));
  });

  /* ---------- upload ---------- */
  $('#sigUpload').addEventListener('change', async (e) => {
    const f = e.target.files[0];
    if (!f) return;
    try {
      uploaded = await prepareUpload(f);
      const img = $('#sigUploadPreview');
      img.src = uploaded;
      img.hidden = false;
    } catch (err) {
      toast('Could not read that image.', 'error');
    }
  });

  /** Uploaded signature: orientation-corrected, downscaled to <=1000px, near-white made transparent, trimmed. */
  async function prepareUpload(f) {
    const url = await imageFileToDataURL(f, 1000);
    const img = await UI.loadImage(url);
    const c = document.createElement('canvas');
    c.width = img.naturalWidth;
    c.height = img.naturalHeight;
    const cx = c.getContext('2d');
    cx.drawImage(img, 0, 0);
    try {
      const id = cx.getImageData(0, 0, c.width, c.height);
      const d = id.data;
      for (let i = 0; i < d.length; i += 4) {
        if (d[i] > 235 && d[i + 1] > 235 && d[i + 2] > 235) d[i + 3] = 0;
      }
      cx.putImageData(id, 0, 0);
    } catch (e) { return url; }
    return trimCanvas(c) || url;
  }

  /* ---------- saved ---------- */
  function renderSaved() {
    const list = store.get(STORE_KEY, []);
    $('#savedTab').hidden = !list.length;
    const wrap = $('#savedSigs');
    wrap.innerHTML = '';
    list.forEach((url, i) => {
      const item = el('div', 'saved-sig' + (savedPick === url ? ' on' : ''));
      item.innerHTML = `<button type="button" class="pick-sig" aria-pressed="${savedPick === url}" aria-label="Saved signature ${i + 1}"><img alt=""></button>`
        + `<button type="button" class="del" title="Remove" aria-label="Remove saved signature ${i + 1}">${icon('x')}</button>`;
      item.querySelector('img').src = url;
      item.querySelector('.del').addEventListener('click', () => {
        const l = store.get(STORE_KEY, []);
        l.splice(i, 1);
        store.set(STORE_KEY, l);
        if (savedPick === url) savedPick = null;
        renderSaved();
        if (!l.length) setTab('draw', true);
        else { const b = $$('#savedSigs .pick-sig')[Math.min(i, l.length - 1)]; if (b) b.focus(); }
      });
      item.querySelector('.pick-sig').addEventListener('click', () => {
        savedPick = url;
        renderSaved();
        const b = $$('#savedSigs .pick-sig')[i];
        if (b) b.focus();
      });
      wrap.append(item);
    });
  }

  /* ---------- tabs ---------- */
  function setTab(t, focusTab) {
    tab = t;
    $$('#signTabs [role=tab]').forEach((b) => {
      const on = b.dataset.tab === t;
      b.classList.toggle('on', on);
      b.setAttribute('aria-selected', String(on));
      b.tabIndex = on ? 0 : -1;
      if (on && focusTab) b.focus();
    });
    $$('#signModal .tab-pane').forEach((p) => { p.hidden = p.dataset.pane !== t; });
    $('#sigRemember').parentElement.style.visibility = t === 'saved' ? 'hidden' : '';
    if (t === 'draw') requestAnimationFrame(sizePad);
    if (t === 'type' && !focusTab) setTimeout(() => $('#sigName').focus(), 0);
  }
  $('#signTabs').addEventListener('click', (e) => {
    const b = e.target.closest('[role=tab]');
    if (b) setTab(b.dataset.tab);
  });
  $('#signTabs').addEventListener('keydown', (e) => {
    const tabs = $$('#signTabs [role=tab]').filter((b) => !b.hidden);
    const i = tabs.findIndex((b) => b.dataset.tab === tab);
    let j = -1;
    if (e.key === 'ArrowRight') j = (i + 1) % tabs.length;
    else if (e.key === 'ArrowLeft') j = (i - 1 + tabs.length) % tabs.length;
    else if (e.key === 'Home') j = 0;
    else if (e.key === 'End') j = tabs.length - 1;
    if (j < 0) return;
    e.preventDefault();
    setTab(tabs[j].dataset.tab, true);
  });

  /* ---------- output ---------- */
  function trimCanvas(c) {
    const w = c.width, h = c.height;
    const data = c.getContext('2d').getImageData(0, 0, w, h).data;
    let x0 = w, y0 = h, x1 = -1, y1 = -1;
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        if (data[(y * w + x) * 4 + 3] > 8) {
          if (x < x0) x0 = x;
          if (x > x1) x1 = x;
          if (y < y0) y0 = y;
          if (y > y1) y1 = y;
        }
      }
    }
    if (x1 < 0) return null;
    const pad = 6;
    x0 = Math.max(0, x0 - pad); y0 = Math.max(0, y0 - pad);
    x1 = Math.min(w - 1, x1 + pad); y1 = Math.min(h - 1, y1 + pad);
    const out = document.createElement('canvas');
    out.width = x1 - x0 + 1;
    out.height = y1 - y0 + 1;
    out.getContext('2d').drawImage(c, x0, y0, out.width, out.height, 0, 0, out.width, out.height);
    return out.toDataURL('image/png');
  }

  async function produce() {
    if (tab === 'saved') return savedPick;
    if (tab === 'upload') return uploaded;
    if (tab === 'draw') {
      if (!strokes.length) return null;
      const r = pad.getBoundingClientRect();
      const scale = 3;
      const c = document.createElement('canvas');
      c.width = Math.round(r.width * scale);
      c.height = Math.round(r.height * scale);
      const cx = c.getContext('2d');
      strokes.forEach((s) => drawStroke(cx, s, scale));
      return trimCanvas(c);
    }
    const name = $('#sigName').value.trim();
    if (!name) return null;
    const size = 120;
    try { await document.fonts.load(`${size}px "${font}"`); } catch (e) { /* fall back to cursive */ }
    const c = document.createElement('canvas');
    const cx = c.getContext('2d');
    const fontDecl = `${size}px "${font}", cursive`;
    cx.font = fontDecl;
    c.width = Math.ceil(cx.measureText(name).width + size);
    c.height = Math.ceil(size * 1.8);
    cx.font = fontDecl;
    cx.fillStyle = color;
    cx.textBaseline = 'middle';
    cx.fillText(name, size / 2, c.height / 2);
    return trimCanvas(c);
  }

  $('#sigUse').addEventListener('click', async () => {
    const url = await produce();
    if (!url) {
      toast(tab === 'type' ? 'Type your name first.' : tab === 'upload' ? 'Choose an image first.' : tab === 'saved' ? 'Pick a saved signature.' : 'Draw your signature first.');
      return;
    }
    const remember = $('#sigRemember').checked;
    if (tab !== 'saved') store.set(REMEMBER_KEY, remember);
    if (tab !== 'saved' && remember) {
      const list = store.get(STORE_KEY, []).filter((u) => u !== url);
      list.unshift(url);
      let saved = false;
      // If storage is full, drop the oldest saved signatures before giving up.
      for (let n = Math.min(4, list.length); n >= 1 && !saved; n--) saved = store.set(STORE_KEY, list.slice(0, n));
      if (!saved) toast('Couldn\'t save the signature on this device (storage full or blocked).', 'error');
    }
    close(url);
  });

  function close(result) {
    modal.hidden = true;
    inerted.forEach((n) => { n.inert = false; });
    inerted = [];
    const r = resolver;
    resolver = null;
    if (prevFocus && document.contains(prevFocus)) { try { prevFocus.focus(); } catch (e) { /* ignore */ } }
    prevFocus = null;
    if (r) r(result || null);
  }
  // Close on a real backdrop click only (not a text selection that ends over the backdrop).
  modal.addEventListener('pointerdown', (e) => { downOnBackdrop = e.target === modal; });
  modal.addEventListener('click', (e) => {
    if (e.target.closest('[data-close]')) { close(null); return; }
    if (e.target === modal && downOnBackdrop) close(null);
    downOnBackdrop = false;
  });
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && !modal.hidden) {
      e.preventDefault();
      e.stopImmediatePropagation(); // keep the editor's Escape handler from also running
      close(null);
    }
  }, true);
  window.addEventListener('resize', () => { if (!modal.hidden && tab === 'draw') sizePad(); });

  function open() {
    if (resolver) { const r = resolver; resolver = null; r(null); }
    strokes = [];
    uploaded = null;
    savedPick = null;
    $('#sigUploadPreview').hidden = true;
    $('#sigUpload').value = '';
    $('#sigRemember').checked = store.get(REMEMBER_KEY, false) === true;
    if (modal.hidden) prevFocus = document.activeElement;
    modal.hidden = false;
    if (!inerted.length) {
      inerted = $$('.view, .site-header').filter((n) => !n.inert);
      inerted.forEach((n) => { n.inert = true; });
    }
    const saved = store.get(STORE_KEY, []);
    if (saved.length) savedPick = saved[0];
    renderSaved();
    setTab(saved.length ? 'saved' : 'draw', true);
    updateTypePreview();
    return new Promise((res) => { resolver = res; });
  }

  window.Signature = { open };
})();
