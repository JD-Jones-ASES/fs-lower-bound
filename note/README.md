# arXiv submission package

This folder mirrors the layout arXiv expects inside the uploaded archive:
`main.tex` at the top level, ancillary files in `anc/`.

- `main.tex` — the paper. Self-contained: the bibliography is inline
  (`thebibliography`), so no `.bbl` is needed and arXiv's AutoTeX compiles it
  with pdflatex directly.
- `anc/verify.py` — a copy of the repository root `verify.py`, shipped as an
  arXiv ancillary file (arXiv lists everything under `anc/` as "Ancillary
  files" next to the paper). The root copy is canonical; if it ever changes,
  re-copy it here.

## Build locally

```
latexmk -pdf main.tex
```

## Package for arXiv

Zip the *contents* of this folder (not the folder itself), excluding this
README and build artifacts, so `main.tex` sits at the archive root:

```
Compress-Archive -Path main.tex, anc -DestinationPath fs-lower-bound-arxiv.zip -Force
```

## Submission checklist

1. Both repos (`fs-lower-bound`, `fs-lower-bound-lean`) must be public before
   the paper announces — it links to them.
2. Fill in the author email in `main.tex` (TODO comment near `\author`).
3. Category: `math.NT` primary, cross-list `math.CO`.
4. License: chosen at submission. arXiv's non-exclusive license keeps journal
   options open; CC BY-SA 4.0 is the house default.
5. A new arXiv account may need endorsement for `math.NT` — arXiv says so at
   submission time if it applies.
6. After the arXiv id exists: add a `preferred-citation` block to
   `CITATION.cff` and link the abstract page from the root README.
