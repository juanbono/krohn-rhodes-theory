# Blueprint

Human-readable mathematical companion to the Lean formalization, written
chapter-by-chapter *before* the corresponding Lean (spec §6).

- `src/print.tex` — self-contained LaTeX entry point: `latexmk -pdf print.tex`.
- `src/chapters/` — one file per theory layer, mirroring `KRTheory/`.
- `\lean{...}` names the Lean declaration; `\leanok` marks it formalized.

TODO(post-v1 or when publishing): migrate preamble to the `leanblueprint`
toolchain (plastex web build + dependency graph). Chapter sources are
already written in its macro dialect, so migration is preamble-only.
