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
- `anc/lean/` — source snapshot of fs-lower-bound-lean at commit `2e6c33c`
  (the completed formalization): all `.lean` files, `lakefile.toml`,
  `lean-toolchain`, `lake-manifest.json`, README, LICENSE. 262 KB. The repo
  is canonical; this is the archival copy that travels with the paper.

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
2. Author name: **JD Jones** in the paper and in the submission's Authors
   metadata field, matching the public identity (the Algebra book, LICENSE,
   the GitHub org). The account name (Joshua Jones) governs the account, not
   the byline; JD is the short form of the legal name, not a pseudonym.
3. Category: `math.NT` primary, cross-list `math.CO` (matches Green–Sawhney,
   the problem's home literature, and the paper's MSC 11B30).
4. License: chosen at submission. arXiv's non-exclusive license keeps journal
   options open; CC BY-SA 4.0 is the house default.
5. A new arXiv account may need endorsement for the primary category
   (`math.NT`) — arXiv says so at submission time if it applies.
6. After the arXiv id exists: add a `preferred-citation` block to
   `CITATION.cff` and link the abstract page from the root README.
