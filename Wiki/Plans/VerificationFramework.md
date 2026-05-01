# Plan: Auditable edges and paper-driven proof skeletons

## Goal

Make every "edge in the universality graph" a top-level Lean term that a human can verify *by reading the type alone*: the two machines, the encode function, and any open hypotheses must all be visible at the top level. Make every paper-derived proof traceable lemma-by-lemma to the paper's own structure.

## Motivation

Two failure modes are possible today even with the existing trust model in [`ProofIntegrity`](../Concepts/ProofIntegrity.md):

1. **Buried `sorry` inside a `Simulation` field.** Historically, `tagToCTSSimulation` in `Lean/Proofs/TagSystemToCyclicTagSystem.lean` ended with `halting := by intro config h_step; sorry`. The integrity check caught this transitively (it reported `sorryAx` in the closure), but a reader skimming the file might not see the gap, and the `Simulation` looked complete from the type signature. This was retired by deleting the dead reference definition: `edge_TagtoCTS` already constructs the simulation directly using `tagToCTSCommutes` plus an explicit `hHalt` hypothesis, exposing the conditionality at the top level.
2. **Stealth-conditional definitions.** `tmToGSSimulation machine hSim hHead` takes `hSim : MooreStepSimulation machine` as a parameter. `MooreStepSimulation` is the actual content of Moore's Theorem 7. There is no Lean theorem in the project that proves it unconditionally — only `stepCommutes` for the nonempty-tape case. From outside, the edge looks proved; in fact, an empty-tape gap is hidden in the precondition.

The current trust model makes hidden assumptions *detectable* (via `CollectAxioms`); this plan makes them *un-hidable* by structural convention.

A separate concern: paper-derived proofs sometimes drift from the paper's structure during formalization, so it becomes hard to tell, lemma by lemma, whether the formal proof still tracks the paper. We want a faithful per-lemma audit.

## Two proposals

### Proposal 1 — Auditable edges

Convention to add to [`ProofIntegrity`](../Concepts/ProofIntegrity.md):

> **Rule 9 — Top-level hypotheses.** Every registered edge is a Lean term whose *single* type signature exposes (a) the source `ComputationalMachine`, (b) the target `ComputationalMachine`, (c) any external hypotheses as named `Prop`-valued parameters with paper references in their docstrings. No `sorry` may appear inside a `Simulation` or `HaltingSimulation` field — gaps must be exposed as parameters.

Implementation:

- New module `Lean/Edges.lean` with a `RegisteredEdge` record bundling source, target, the simulation term, and metadata (paper ref + hypothesis list).
- One central registry: `def edges : List RegisteredEdge`, plus `def conditionalEdges : List ConditionalEdge` for those that take hypotheses.
- Extend `Lean/Integrity.lean`: enumerate the registry; for each edge print machines, paper ref, hypothesis Props, axiom closure.
- Existing definitions that hide `sorry` in fields are split: the `Simulation` is defined unconditionally and takes the open hypothesis as an explicit `Prop` parameter.

This does not require new Lean machinery — `Simulation A B` is already correct. It standardises the *shape* of the call site so a human reading `Lean/Edges.lean` sees the audit trail in one screen.

### Proposal 2 — Paper-driven proof skeleton

For each paper-derived proof, add:

```
Wiki/Proofs/<Name>/
  Skeleton.md          # the paper's own lemma DAG
  Lemmas/
    <NN>_<title>.md    # one per lemma node
```

`Skeleton.md` lists the lemma nodes in the order the paper proves them, with:
- Paper section/page/equation references
- Dependency edges (which other lemmas it uses)
- Tags for **basic notions** (vocabulary terms the paper introduces — e.g. "DOD", "active cell", "shift magnitude")
- Per-node Lean status: `Stated | Sorry | Proved | Hypothesis`
- Per-node Lean theorem name (when formalized)

Per-node files (`Lemmas/<NN>_<title>.md`) carry: math statement, paper proof outline, dependencies (back-pointers), basic notions used, Lean theorem path, status.

**Discipline for new proofs:** always extract the skeleton *first*, before any Lean coding. **Do not invent new structure** — the formalization mirrors the paper. Prove leaves first; once a node is `Proved` (sorry-free), do not return to alter its statement. This protects already-discharged dependencies from drifting under your feet.

For existing proofs we extract the skeleton retroactively as an audit step.

## Steps

- [x] Confirm baseline: `lake build` green, `Integrity.lean` reports current axiom traces
- [ ] Stage 1 — Embed framework
  - [ ] Write this plan
  - [ ] Create `Lean/Edges.lean` (record types + initial registry skeleton)
  - [ ] Create `Wiki/Proofs/<Name>/` template (use ECA Mirror as the worked example)
- [ ] Stage 2 — Demonstrate on ECA Mirror (smallest existing proof)
  - [ ] Extract paper skeleton (or, since this is one-paragraph folklore, sketch it)
  - [ ] Register the two edges (110→124, 124→110) in `Lean/Edges.lean`
  - [ ] Verify build + integrity pass
- [ ] **Stage 3 — Pause for user review of the demonstration**
- [x] Stage 4 — Roll out to other proofs (approved 2026-04-27)
  - [x] TM → GS (Moore Theorem 7) — `edge_TMtoGS` registers `tmToGSSimulation` with `hSim`, `hHead` at top level
  - [x] GS → TM (Moore Theorem 8) — `edge_GStoTM` rebuilds Simulation via `gsToTMCommutes` + `hHalt`, avoiding the buried sorry in `gsToTMSimulation`
  - [x] Tag → CTS (Cook 2004) — `edge_TagtoCTS` hoists the single-element halting case to top-level `hHalt`
  - [x] CockeMinsky chain — `edge_CockeMinskyChain` registers `wolfram23Universal` with `h_cm`, `h_smith`
  - [ ] Add Rule 9 to [`ProofIntegrity`](../Concepts/ProofIntegrity.md) once stable (requires human approval per Rule 8)

## Decisions

- **`axiom` vs hypothesis parameter for external assumptions.** Use parameters (current convention from `ProofIntegrity` Rule 3). Custom axioms are forbidden by Rule 3; we keep that.
- **Where to store the registry.** A single `Lean/Edges.lean` (importing all proof files) imported by `Lean/Integrity.lean`. The integrity check then enumerates without grep.
- **Granularity of skeleton lemmas.** Match the paper's lemmas. Do not split the paper's lemmas into smaller pieces unless a notational obstacle forces it; if you do, document the split in the skeleton.
- **Smith hypothesis stays a hypothesis.** Per user instruction, we will not attempt to prove `SmithSimulation`. It remains a top-level parameter of `wolfram23Universal`.

## History

| Date | Actor | Action |
|---|---|---|
| 2026-04-27 | LLM | Created plan; awaiting Stage 2 review |
| 2026-04-27 | Human | Approved rollout; instructed to skip stuck proofs with sorry rather than cycling |
| 2026-04-27 | LLM | Stage 4 done: 6 edges registered, all wrappers sorry-free, per-proof skeletons written, EdgeAudit reports PASS |
