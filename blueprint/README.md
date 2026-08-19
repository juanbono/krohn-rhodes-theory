# Blueprint

Human-readable mathematical companion to the Lean formalization, written
chapter-by-chapter *before* the corresponding Lean (spec §6).

- `src/print.tex` — self-contained LaTeX entry point: `latexmk -pdf print.tex`.
- `src/chapters/` — one file per theory layer, mirroring `KRTheory/`.
- `\lean{...}` names the Lean declaration; `\leanok` marks it formalized.

Two build paths:

- `latexmk -pdf print.tex` (from `src/`) — the PDF, pdflatex.
- `leanblueprint web` (from the repo root) — the web version with the
  dependency graph. Needs `pip install -r blueprint/requirements.txt`
  AND a TeX installation: plasTeX resolves `\input` via `kpsewhich`, so
  without TeX every chapter silently fails to load.

`leanblueprint checkdecls` verifies every `\lean{...}` name exists; it
needs a built project (`lake build`) and a prior `leanblueprint web`.

Publishing the web version to GitHub Pages is deliberately not wired up
(a publication decision, not a correctness one); CI builds it and
uploads it as an artifact.
