# Wiki Index

Knowledge base for the Universality Graph project. Maintained by the LLM after each substantial step.

## Status & Log

- [Status](Status.md) — current state of the repo: proved edges, open sorries, next steps
- [Activity Log](Log.md) — chronological record of LLM actions and human revisions

## Plans

- [Current Focus](Plans/CurrentFocus.md) — closing GS → TM last sorry
- [GS→TM General Width](Plans/GStoTM_GeneralWidth.md) — extending step simulation to all window widths
- [Next Edges](Plans/NextEdges.md) — candidates for the next formalization target
- [Action Items](Plans/ActionItems.md) — next steps and TODOs
- [Verification Framework](Plans/VerificationFramework.md) — auditable edges (Lean/Edges.lean) and paper-driven proof skeletons


## Tour

Interactive guided walk through the project — say **"start tour"** to begin. Tour data lives in `Tour/` (local, gitignored). See CLAUDE.md § Guided Tour for the protocol.

## Systems

- [Turing Machine](Systems/TuringMachine.md) — one-sided and bi-infinite tape variants, Wolfram's (2,3) UTM
- [Generalized Shift](Systems/GeneralizedShift.md) — Moore's data-dependent window shifts on bi-infinite tapes
- [Tag System](Systems/TagSystem.md) — 2-tag systems: delete 2, append production
- [Cyclic Tag System](Systems/CyclicTagSystem.md) — binary data with phase-cycled appendants
- [Elementary Cellular Automaton](Systems/ElementaryCellularAutomaton.md) — 1D nearest-neighbor CAs (Rules 110, 124, 137)

## Proofs (edges in the graph)

- [TM → GS](Proofs/TMtoGS.md) — Moore Theorem 7, σ=1 τ=1, fully proved
  - [TM → GS Skeleton](Proofs/TMtoGS/Skeleton.md) — paper-driven layered DAG
- [GS → TM](Proofs/GStoTM.md) — Moore Theorem 8, σ=1 τ≤2(w-1)+m, fully proved (w=1)
  - [GS → TM Skeleton](Proofs/GStoTM/Skeleton.md) — paper-driven layered DAG
- [Tag → CTS](Proofs/TagToCTS.md) — Cook's encoding, fully proved
  - [Tag → CTS Skeleton](Proofs/TagToCTS/Skeleton.md) — paper-driven layered DAG
- [Cocke-Minsky Chain](Proofs/CockeMinskyChain.md) — TM → Tag → CTS → (2,3) TM, hypotheses remain
  - [Cocke-Minsky Chain Skeleton](Proofs/CockeMinskyChain/Skeleton.md) — paper-driven layered DAG
- [ECA Mirror](Proofs/ECAMirror.md) — Rule 110 ↔ 124 via tape reversal, fully proved
  - [ECA Mirror Skeleton](Proofs/ECAMirror/Skeleton.md) — paper-driven layered DAG (demo of new framework)
- [ECA Conjugation](Proofs/ECAConjugation.md) — Klein-4 framework: mirror, complement, combined; orbit of Rule 110 = {110, 124, 137, 193}, fully proved

## Concepts

- [Computational Machine](Concepts/ComputationalMachine.md) — the vertex type (Config + step)
- [Simulation Encoding](Concepts/SimulationEncoding.md) — three layered structures: `HaltingSimulation`, `Simulation`, `SimulationEncoding` (conjugation form)
- [Overhead](Concepts/Overhead.md) — spatial and temporal cost of simulation
- [Pipeline Architecture](Concepts/PipelineArchitecture.md) — LLM pipeline for auto-expanding the graph (future)
- [Lean Blueprint](Concepts/LeanBlueprint.md) — PFR-style blueprint with `\lean{}` annotations
- [Proof Integrity](Concepts/ProofIntegrity.md) — trust model for LLM-generated Lean proofs: locked goals, no axioms, sorry tracking, native_decide policy, cross-validation

## Notebooks

- [TM ↔ GS](Notebooks/TM_GS.md) — Moore 1991, TM ↔ Generalized Shift demonstration
- [Cocke-Minsky Chain](Notebooks/CockeMinsky.md) — TM → Tag → CTS → (2,3) TM
- [ECA Symmetries](Notebooks/ECASymmetries.md) — Klein-4 conjugations of ECA rules (mirror, complement, combined)
- [Universality Graph](Notebooks/UniversalityGraph.md) — graph exploration and visualization
- [Cross-Validation](Notebooks/CrossValidation.md) — Lean vs. Wolfram definition validation

## Resources (papers, repos, tools)

- [Moore 1991](Resources/Moore1991.md) — generalized shifts ↔ Turing machines
- [Cook 2004](Resources/Cook2004.md) — Rule 110 universality via cyclic tag systems
- [Smith 2007](Resources/Smith2007.md) — (2,3) TM universality
- [Neary & Woods 2006](Resources/Neary2006.md) — polynomial-overhead Rule 110 universality
- [Woods & Neary 2009](Resources/WoodsNeary2009.md) — survey of small universal TMs
- [Wolfram 2022](Resources/Wolfram2022.md) — physicalization of metamathematics / ruliad
- [Miranda-Ramos et al. 2025](Resources/Miranda2025.md) — billiards compute (potential future vertex)
- [Polu & Sutskever 2020](Resources/Polu2020.md) — GPT-f for automated theorem proving
- [Zheng et al. 2025](Resources/Zheng2025.md) — AI for mathematics survey
