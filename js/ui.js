/* Shared UI helpers */
(function () {
  'use strict';

  const $ = (s, r = document) => r.querySelector(s);
  const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));

  function el(tag, cls, html) {
    const n = document.createElement(tag);
    if (cls) n.className = cls;
    if (html != null) n.innerHTML = html;
    return n;
  }

  function icon(name) {
    return `<svg><use href="#i-${name}"/></svg>`;
  }

  let busyCount = 0;
  let busyInert = [];
  function setBusyInert(on) {
    // Keep keyboard focus from reaching controls behind the busy overlay.
    if (on) {
      busyInert = $$('.view:not([hidden]), .site-header, #signModal:not([hidden])').filter((n) => !n.inert);
      busyInert.forEach((n) => { n.inert = true; });
    } else {
      busyInert.forEach((n) => { n.inert = false; });
      busyInert = [];
    }
  }
  function busy(msg) {
    const b = $('#busy');
    if (msg === false) {
      busyCount = Math.max(0, busyCount - 1);
      if (!busyCount) {
        b.hidden = true;
        document.body.removeAttribute('aria-busy');
        setBusyInert(false);
      }
      return;
    }
    busyCount++;
    $('#busyMsg').textContent = msg || 'Working…';
    if (b.hidden) {
      b.hidden = false;
      document.body.setAttribute('aria-busy', 'true');
      setBusyInert(true);
    }
  }
  function isBusy() { return busyCount > 0; }

  function toast(msg, type, ms) {
    const t = el('div', 'toast' + (type ? ' ' + type : ''));
    t.setAttribute('role', type === 'error' ? 'alert' : 'status');
    t.title = 'Click to dismiss';
    t.textContent = msg;
    t.addEventListener('click', () => t.remove());
    $('#toasts').append(t);
    setTimeout(() => t.remove(), ms || (type === 'error' ? 6000 : 3500));
  }

  function readAsDataURL(file) {
    return new Promise((res, rej) => {
      const r = new FileReader();
      r.onload = () => res(r.result);
      r.onerror = () => rej(r.error);
      r.readAsDataURL(file);
    });
  }

  function loadImage(src) {
    return new Promise((res, rej) => {
      const img = new Image();
      img.onload = () => res(img);
      img.onerror = () => rej(new Error('Could not load image'));
      img.src = src;
    });
  }

  /** JPEG EXIF orientation (1-8), or 1 when absent/unreadable. */
  async function jpegOrientation(file) {
    try {
      const v = new DataView(await file.slice(0, 128 * 1024).arrayBuffer());
      if (v.getUint16(0) !== 0xFFD8) return 1;
      let off = 2;
      while (off + 4 < v.byteLength) {
        const marker = v.getUint16(off);
        const len = v.getUint16(off + 2);
        if (marker === 0xFFE1 && v.getUint32(off + 4) === 0x45786966) { // "Exif"
          const t = off + 10;
          const le = v.getUint16(t) === 0x4949;
          const ifd = t + v.getUint32(t + 4, le);
          const n = v.getUint16(ifd, le);
          for (let i = 0; i < n; i++) {
            const e = ifd + 2 + i * 12;
            if (v.getUint16(e, le) === 0x0112) return v.getUint16(e + 8, le) || 1;
          }
          return 1;
        }
        if ((marker & 0xFF00) !== 0xFF00 || marker === 0xFFDA) break;
        off += 2 + len;
      }
    } catch (e) { /* ignore */ }
    return 1;
  }

  /**
   * Read an image file and return a PNG or JPEG data URL (formats pdf-lib can embed).
   * Images are redrawn through a canvas when needed so that the pixels match what the
   * browser displays (EXIF orientation applied - pdf-lib ignores EXIF) and so that very
   * large photos are capped at maxSide pixels on the longest edge.
   */
  async function imageFileToDataURL(file, maxSide = 2000) {
    const url = await readAsDataURL(file);
    const isPng = /^data:image\/png/.test(url);
    const isJpeg = /^data:image\/jpe?g/.test(url);
    const orient = isJpeg ? await jpegOrientation(file) : 1;
    const img = await loadImage(url); // browsers apply EXIF orientation when drawing
    const w = img.naturalWidth, h = img.naturalHeight;
    const scale = Math.min(1, maxSide / Math.max(w, h));
    if ((isPng || isJpeg) && orient === 1 && scale === 1) return url;
    const c = document.createElement('canvas');
    c.width = Math.max(1, Math.round(w * scale));
    c.height = Math.max(1, Math.round(h * scale));
    const cx = c.getContext('2d');
    if (isJpeg) { cx.fillStyle = '#fff'; cx.fillRect(0, 0, c.width, c.height); }
    cx.drawImage(img, 0, 0, c.width, c.height);
    return isJpeg ? c.toDataURL('image/jpeg', 0.92) : c.toDataURL('image/png');
  }

  function downloadBlob(data, name, type) {
    const blob = data instanceof Blob ? data : new Blob([data], { type: type || 'application/pdf' });
    const url = URL.createObjectURL(blob);
    const a = el('a');
    a.href = url;
    a.download = name;
    document.body.append(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 30000);
  }

  // Files confirmed as PDFs by their magic bytes (e.g. extension-less Android/WhatsApp files).
  const sniffedPdfs = new WeakSet();
  function isPdf(file) {
    return !!file && (file.type === 'application/pdf' || /\.pdf$/i.test(file.name) || sniffedPdfs.has(file));
  }
  /** Async check that also looks for the %PDF- header when the name/type don't say PDF. */
  async function isPdfAsync(file) {
    if (!file) return false;
    if (isPdf(file)) return true;
    if (file.type && !/^application\/(octet-stream|x-pdf|acrobat|binary)$/.test(file.type)) return false;
    try {
      const head = new Uint8Array(await file.slice(0, 1024).arrayBuffer());
      if (new TextDecoder('latin1').decode(head).includes('%PDF-')) { sniffedPdfs.add(file); return true; }
    } catch (e) { /* unreadable */ }
    return false;
  }
  async function filterPdfs(files) {
    const list = Array.from(files || []);
    const ok = await Promise.all(list.map(isPdfAsync));
    return list.filter((_, i) => ok[i]);
  }

  function baseName(name) {
    return (name || 'document').replace(/\.pdf$/i, '');
  }

  const store = {
    get(key, fallback) {
      try {
        const v = localStorage.getItem(key);
        return v == null ? fallback : JSON.parse(v);
      } catch (e) {
        return fallback;
      }
    },
    set(key, value) {
      try {
        localStorage.setItem(key, JSON.stringify(value));
        return true;
      } catch (e) { return false; /* storage unavailable or full */ }
    },
  };

  window.UI = { $, $$, el, icon, busy, isBusy, toast, readAsDataURL, loadImage, imageFileToDataURL, downloadBlob, isPdf, isPdfAsync, filterPdfs, baseName, store };
})();
