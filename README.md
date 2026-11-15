# Pagecraft — PDF editor

A Sejda-style PDF editor that runs entirely in the browser. Files never leave your device.

## Features
- **Edit existing text** in place: only the changed glyphs are replaced, using the document's own font, size and colour
- Add text, images and signatures (draw / type / upload), white-out, highlight, freehand drawing and shapes
- Undo / redo, zoom, keyboard shortcuts
- Pages: reorder (drag), rotate, duplicate, insert blank, delete, organize grid
- **Batch edit**: open many PDFs as separate documents, swipe between them, download all as a ZIP
- Merge, split (every page / every N / ranges) and extract pages

## Run locally
It's a static site with no build step. Serve the folder with any static server, for example:

```bash
npx serve .
```

Then open the printed URL.

## Built with
[pdf.js](https://mozilla.github.io/pdf.js/), [pdf-lib](https://pdf-lib.js.org/), [fabric.js](http://fabricjs.com/), [JSZip](https://stuk.github.io/jszip/) (loaded from cdnjs).
