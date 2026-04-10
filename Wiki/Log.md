# Activity Log

| Date | Actor | Action |
|---|---|---|
| 2026-04-10 | LLM | Added proof integrity system: rules in CLAUDE.md, trust model in Wiki/Concepts/ProofIntegrity.md, Lean/Integrity.lean (CollectAxioms + leanchecker), Scripts/verify_integrity.sh, CrossValidation notebook, updated Status.md with full inventories, updated README |
| 2026-04-08 | LLM | Added agentic team member to README, created Wiki/Plans/ActionItems.md with next steps |
| 2026-04-06 | LLM | GS→TM general width: TMPhase refactor, bridge lemma proved, stepSimulation wired for all w. 1 sorry remains in read+write phase loop (fullSim_general). |
| 2026-04-06 | LLM | Updated wiki (Status, GStoTM, Moore1991) for accurate overhead/w=1 status; updated Wolfram graph edges (added Tag→CTS, fixed GS→TM τ); updated README with verified-edges table |
| 2026-04-06 | LLM | Closed last sorry in GS→TM: refactored Nat state to TMPhase inductive, proved stepSimulation_w1. Build: 0 sorry, 0 axiom. |
| 2026-04-05 | LLM | Created wiki with 22 seed articles across Systems/, Proofs/, Concepts/, Papers/ |
| 2026-04-05 | LLM | Added Plans/, Log.md, and revision workflow to CLAUDE.md |
| 2026-04-05 | LLM | Added Tour/ system: guided interactive walk with .wl code generation |
| 2026-04-05 | LLM | Renamed Wiki/Papers/ → Wiki/Resources/; moved Resources/*.md into wiki; Resources/ now on-demand (gitignored) |
| 2026-04-05 | LLM | Added Polu2020, Zheng2025, PipelineArchitecture, LeanBlueprint wiki articles |
| 2026-04-05 | LLM | Tour/ now created on demand (not pre-created) |
| 2026-04-05 | LLM | Simplified revision: wiki prose auto-maintained, revision for code/functionality only |
| 2026-04-05 | LLM | Added ## Recover sections to all resource articles; resource pipeline documented |
| 2026-04-05 | LLM | Created KnowledgeBasePlugin.md plan for extracting workflow as reusable plugin |
| 2026-04-05 | LLM | Moved Notebooks/*.md → Wiki/Notebooks/; Notebooks/ now fully generated (gitignored) |
| 2026-04-05 | LLM | Added notebook-create skill (skill 8) to plugin plan |
| 2026-04-05 | LLM | Updated all Scripts/ to read from Wiki/Notebooks/ and Wiki/Resources/ |
