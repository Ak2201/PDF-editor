/* Landing page + routing */
(function () {
  'use strict';
  const { $, $$, toast, filterPdfs, isBusy } = UI;

  let opening = false; // guards against a second open while a file is still loading

  function view() { return document.body.dataset.view; }

  /* ---------- history: let the browser/Android Back button return home ---------- */
  function pushView(v) {
    if (v === 'home') return;
    const st = history.state;
    if (st && st.view === v) return;
    if (st && st.view && st.view !== 'home') history.replaceState({ view: v }, '', '#' + v);
    else history.pushState({ view: v }, '', '#' + v);
  }
  // Editor.open / Split.open set data-view themselves; mirror entries into history.
  new MutationObserver(() => pushView(view())).observe(document.body, { attributes: true, attributeFilter: ['data-view'] });

  function leave() {
    const v = view();
    if (v === 'editor' && Editor.hasChanges()
      && !confirm('Leave the editor? Changes you haven\'t downloaded will be lost.')) return false;
    if (v === 'editor') Editor.close();
    if (v === 'split' && Split.close) Split.close();
    document.body.dataset.view = 'home';
    window.scrollTo(0, 0);
    return true;
  }

  function goHome() {
    if (view() === 'home') return;
    if (history.state && history.state.view && history.state.view !== 'home') {
      history.back(); // popstate handler does the actual leave/confirm
      return;
    }
    leave();
  }

  window.addEventListener('popstate', () => {
    if (view() === 'home') return;
    if (isBusy()) { pushView(view()); return; }
    if (!leave()) history.pushState({ view: view() }, '', '#' + view()); // cancelled: restore entry
  });
  if (location.hash) history.replaceState({ view: 'home' }, '', location.pathname + location.search);

  function pickFiles(multiple) {
    return new Promise((resolve) => {
      const inp = multiple ? $('#pdfMultiInput') : $('#pdfInput');
      inp.value = '';
      inp.onchange = () => resolve(Array.from(inp.files));
      inp.click();
    });
  }

  async function startTool(tool, files) {
    if (opening || isBusy()) return;
    if (!files) files = await pickFiles(tool !== 'split' && tool !== 'extract');
    if (!files.length) return; // picker cancelled
    if (opening || isBusy()) return;
    opening = true;
    try {
      files = await filterPdfs(files);
      if (!files.length) { toast('Please choose a PDF file.', 'error'); return; }
      if (tool === 'split' || tool === 'extract') return await Split.open(files[0], tool);
      if (tool === 'merge' && files.length === 1) toast('Tip: add more PDFs with the “Add PDF” button in the pages panel.', null, 5000);
      return await Editor.open(files, {
        batch: tool !== 'merge' && files.length > 1, // several files = separate documents (ZIP download)
        tool: tool === 'sign' ? 'sign' : undefined,
        organize: tool === 'organize' || (tool === 'merge' && files.length > 1),
      });
    } finally {
      opening = false;
    }
  }

  $$('[data-tool]').forEach((b) => {
    if (b.closest('#view-editor')) return;
    b.addEventListener('click', (e) => {
      e.preventDefault();
      e.stopPropagation();
      startTool(b.dataset.tool);
    });
  });
  $$('[data-go=home]').forEach((b) => b.addEventListener('click', (e) => { e.preventDefault(); goHome(); }));
  $('#edBack').addEventListener('click', goHome);
  $('#startBlank').addEventListener('click', async (e) => {
    e.stopPropagation();
    if (opening || isBusy()) return;
    opening = true;
    try { await Editor.openBlank(); } finally { opening = false; }
  });

  // drop zone (pointer click on the empty area; keyboard users use the inner Upload button)
  const dz = $('#dropzone');
  dz.addEventListener('click', (e) => { if (e.target === dz || e.target.classList.contains('dz-inner')) startTool('edit'); });

  const hasFiles = (e) => !!e.dataTransfer && Array.from(e.dataTransfer.types || []).includes('Files');
  let depth = 0;
  document.addEventListener('dragenter', (e) => {
    if (view() !== 'home' || !hasFiles(e)) return;
    depth++;
    dz.classList.add('drag');
  });
  document.addEventListener('dragleave', () => {
    if (view() !== 'home') return;
    depth = Math.max(0, depth - 1);
    if (!depth) dz.classList.remove('drag');
  });
  // In every view, stop the browser from navigating away to a dropped file.
  document.addEventListener('dragover', (e) => {
    if (hasFiles(e)) e.preventDefault();
  });
  document.addEventListener('drop', async (e) => {
    if (!hasFiles(e)) return;
    e.preventDefault(); // the editor's own drop handler (on #view-editor) runs before this one
    const v = view();
    if (v === 'editor') return;
    depth = 0;
    dz.classList.remove('drag');
    if (opening || isBusy()) return;
    if (!$('#signModal').hidden) return;
    const files = Array.from(e.dataTransfer.files);
    if (v === 'split') {
      const pdfs = await filterPdfs(files);
      if (!pdfs.length) { toast('Please drop a PDF file.', 'error'); return; }
      if (confirm(`Open “${pdfs[0].name}” in this tool instead of the current file?`)) {
        startTool($('input[name=smode]:checked').value === 'extract' ? 'extract' : 'split', [pdfs[0]]);
      }
      return;
    }
    if (v !== 'home') return;
    const pdfs = await filterPdfs(files);
    if (!pdfs.length) { toast('Please drop a PDF file.', 'error'); return; }
    startTool('edit', pdfs);
  });
})();
