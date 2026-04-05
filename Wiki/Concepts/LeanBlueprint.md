# Lean Blueprint

The project uses a Lean Blueprint (PFR-style) to provide a human-readable overview of the formalization with dependency tracking. Lives in `Blueprint/`.

## Structure

- `web.tex`, `print.tex` — drivers for web and PDF builds
- `chapter/` — one `.tex` file per chapter (introduction, systems, encodings, verified, higher, open, etc.)
- `preamble/` — shared LaTeX macros
- `references.bib` — BibTeX

## Annotations

- `\lean{Namespace.theorem}` — links a statement to its Lean declaration
- `\leanok` — marks a statement as fully formalized (0 sorry)

## Reference

Template based on Terence Tao's PFR project. Upstream: https://github.com/pitmonticone/PFR

## See also

- [ComputationalMachine](ComputationalMachine.md), [SimulationEncoding](SimulationEncoding.md) — the Lean types documented in the blueprint
