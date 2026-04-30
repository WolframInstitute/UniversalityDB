# Project Status

Last updated: 2026-05-01

## Simulation framework

`Lean/SimulationEncoding.lean` defines three templates in increasing strength:
`HaltingSimulation`, `Simulation`, `SimulationEncoding`. `Simulation` is used by
4 edges (canonical, composable); `SimulationEncoding` (the conjugation form) is
used by 1 edge (TM → GS); `HaltingSimulation` is used by `wolfram23HaltingSimulation`.

The dead-code `SimulationViaDecode` (with `roundtrip + normalize` fields) was
removed in favor of `SimulationEncoding`, which carries pure conjugation:
`step_B(b) = decode (step_A^n (encode b))`. Canonicalization, when needed, is
on the *machine* via `stepNormalized` plus a bisimulation lemma — not as a
structure field.

Every machine family has a `toComputationalMachine` wrapper in its `Defs.lean`.
Bi-infinite-tape machines also expose a `stepNormalized` /
`toComputationalMachineNormalized` variant that post-strips trailing zeros from
both tapes (`Lean/Machines/GeneralizedShift/Defs.lean`,
`Lean/Machines/BiInfiniteTuringMachine/Defs.lean`). The TM → GS edge targets
the normalized BiTM, which is what makes the conjugation in `SimulationEncoding`
strict (no `modulo normalize`).

`BiInfiniteTuringMachine.step_stripConfig_bisim` proves the bisimulation
`(step c).map stripConfig = stepNormalized (stripConfig c)` — i.e., the
standard `step` is well-defined modulo trailing-zero canonicalization. The
analogous lemma for `GeneralizedShift.step` is structurally similar
(induction over `shiftBy` with single-step bisimulations on
`shiftRightOne`/`shiftLeftOne`); `stripConfig_idempotent` is proved and the
chain is documented in-file. Lean formalization of the GS shift bisim is
deferred — paper-and-pencil-clear, tedious case analysis (cells × right tape
× left tape branches).

## Proved edges

| Edge | File | Template | Overhead | Sorry in proof |
|---|---|---|---|---|
| TM → GS (Moore Thm 7) | `Lean/Proofs/TMtoGS.lean` | `SimulationEncoding` (conjugation) | σ=1, τ=1 | 0 (4 well-formedness hypotheses) |
| GS → TM (Moore Thm 8) | `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | `Simulation` | σ=1, τ≤2(w-1)+m | 2 (`fullSim_general` for w≥2; `gsToTMSimulation` reconstructed at wrapper) |
| Tag → CyclicTag (Cook 2004) | `Lean/Proofs/TagSystemToCyclicTagSystem.lean` | `Simulation` | 1 tag step = 2k CTS steps | 1 (halting for single-element tag words) |
| ECA Rule 110 ↔ Rule 124 | `Lean/Proofs/ElementaryCellularAutomatonMirror.lean` | `Simulation` | σ=1, τ=1 | 0 |
| ECA Rule 110 ↔ Rule 137 (complement) | `Lean/Proofs/ElementaryCellularAutomatonConjugation.lean` | `Simulation` | σ=1, τ=1 | 0 |
| ECA Rule 110 ↔ Rule 193 (mirror ∘ complement) | `Lean/Proofs/ElementaryCellularAutomatonConjugation.lean` | `Simulation` | σ=1, τ=1 | 0 |

## Hypothetical edges (stated as hypotheses)

| Edge | File | Hypothesis |
|---|---|---|
| TM → 2-Tag (Cocke-Minsky 1964) | `Lean/Proofs/CockeMinsky.lean` | `CockeMinskyStepSimulation`: every TM step lifts to bounded tag steps |
| CTS → (2,3) TM (Smith 2007) | `Lean/Proofs/CockeMinsky.lean` | `SmithSimulation`: every CTS computation is tracked by the (2,3) TM |

## Main theorem

`wolfram23Universal` in `Lean/Proofs/CockeMinsky.lean`: Wolfram's (2,3) TM is universal, assuming CockeMinsky and Smith hypotheses.

`wolfram23HaltingSimulation`: same result wrapped as a `HaltingSimulation` instance (1 sorry bridging `ComputationalMachine.Halts` ↔ `BiInfiniteTuringMachine.Halts`).

## Proof integrity

Run `Scripts/verify_integrity.sh` to verify. The script uses `CollectAxioms.collect` on every key theorem to check axiom dependencies, `leanchecker` for full kernel replay, and validates that `Integrity.lean` imports match `lakefile.lean` roots. See [ProofIntegrity](Concepts/ProofIntegrity.md) for the full trust model.

## Edge registry

[Lean/Edges.lean](../Lean/Edges.lean) contains the registered edges as named typed wrappers; [Lean/EdgeAudit.lean](../Lean/EdgeAudit.lean) prints an audit trail at build time (machines, paper ref, hypothesis list, axiom closure). **Ten** edges registered (`EDGE AUDIT: PASS (10 edges)` at build time):

| Edge | Status | Top-level hypotheses | Wrapper axioms |
|---|---|---|---|
| `edge_ECA110_ECA124` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA124_ECA110` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA110_ECA137` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA137_ECA110` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA110_ECA193` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA193_ECA110` | unconditional | (none) | propext, Quot.sound |
| `edge_TMtoGS` | conditional (4 well-formedness assumptions) | hk, hHeadAll, hWriteBound, hStateBound — **commutes and halting fully proved** | propext, Quot.sound, Classical.choice |
| `edge_GStoTM` | conditional | `hSim`, `hLen`, `hShift`, `hHalt` | propext |
| `edge_TagtoCTS` | conditional | `hHalt` (single-element tag word case) | propext, Quot.sound, Classical.choice |
| `edge_CockeMinskyChain` | conditional | `h_cm`, `h_smith` | propext, Quot.sound, Classical.choice |

All wrapper closures are sorry-free. The buried sorries from the original proof files (`gsToTMSimulation`, `tagToCTSSimulation` halting, `wolfram23PreservesHalting` bridge) are excluded from the wrapper closures because the wrappers either rebuild the `Simulation` cleanly using existing sorry-free lemmas (e.g. `gsToTMCommutes`) or hoist the missing piece to a top-level `Prop` parameter.

Per-proof paper-driven skeletons under [Wiki/Proofs/<Name>/Skeleton.md](Proofs/) — see the [VerificationFramework](Plans/VerificationFramework.md) plan.

## Machine families in Lean

Each family has a `toComputationalMachine` wrapper and an `iterationStep_eq_exactSteps` compatibility lemma.

- Turing Machine (one-sided): `Lean/Machines/TuringMachine/Defs.lean`
- Bi-infinite Turing Machine: `Lean/Machines/BiInfiniteTuringMachine/Defs.lean`
- Generalized Shift: `Lean/Machines/GeneralizedShift/Defs.lean`
- 2-Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Cyclic Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Elementary Cellular Automaton: `Lean/Machines/ElementaryCellularAutomaton/Defs.lean`

## Simulation framework

`Lean/SimulationEncoding.lean` defines three templates:

| Structure | Fields | Use |
|---|---|---|
| `HaltingSimulation A B` | `encode`, `preserves_halting` | Halting preservation only (e.g. Smith) |
| `Simulation A B` | `encode`, `commutes`, `halting` | Canonical step-level simulation (4 edges). Composes. |
| `SimulationEncoding A B` | `encode`, `decode`, `commutes`, `halting` | Conjugation form `step_B = decode ∘ step_A^n ∘ encode` (TM→GS) |

`Simulation` composes via `Simulation.compose` and derives `halting_preserved`. `HaltingSimulation` composes via `HaltingSimulation.compose`. `SimulationEncoding` is a presentation form for edges with a natural decode; it doesn't compose (and doesn't need to — composition flows through `Simulation`).

## Current focus

GS → TM general width: all building blocks fully proved (readScan, lastRead, writeLoop, writeZeroShift — 0 sorry). One sorry remains in `fullSim_general` — the composition that chains the 4 phases via `exactSteps_append`. See `Wiki/Plans/GStoTM_GeneralWidth.md`.

## See also

- [CockeMinskyChain](Proofs/CockeMinskyChain.md) — the full TM → Tag → CTS → (2,3) TM chain
- [SimulationEncoding](Concepts/SimulationEncoding.md) — the core Lean abstraction
- [ProofIntegrity](Concepts/ProofIntegrity.md) — trust model and verification procedures
