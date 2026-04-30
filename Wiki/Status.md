# Project Status

Last updated: 2026-04-30

## Simulation framework

`Lean/SimulationEncoding.lean` currently defines four templates: `Simulation`,
`SimulationEncoding`, `HaltingSimulation`, `SimulationViaDecode`. Of these,
`Simulation` is used by 4 edges, `SimulationViaDecode` by 1, and the other
two are mostly scaffolding (`HaltingSimulation` is referenced by
`wolfram23HaltingSimulation`, `SimulationEncoding` is currently unused).

Every machine family has a `toComputationalMachine` wrapper in its `Defs.lean`.
Bi-infinite-tape machines also expose a `stepNormalized` /
`toComputationalMachineNormalized` variant that post-strips trailing zeros from
both tapes (`Lean/Machines/GeneralizedShift/Defs.lean`,
`Lean/Machines/BiInfiniteTuringMachine/Defs.lean`). These canonicalize the
representation so the encode of a BiTM config lands in the image-preserving
subset of GS configs — usable for a future unification of all simulations
under a single decode-based template.

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
| TM → GS (Moore Thm 7) | `Lean/Proofs/TMtoGS.lean` | `SimulationViaDecode` | σ=1, τ=1 | 0 (4 well-formedness hypotheses) |
| GS → TM (Moore Thm 8) | `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | `Simulation` | σ=1, τ≤2(w-1)+m | 2 (`fullSim_general` for w≥2; `gsToTMSimulation` reconstructed at wrapper) |
| Tag → CyclicTag (Cook 2004) | `Lean/Proofs/TagSystemToCyclicTagSystem.lean` | `Simulation` | 1 tag step = 2k CTS steps | 1 (halting for single-element tag words) |
| ECA Rule 110 ↔ Rule 124 | `Lean/Proofs/ElementaryCellularAutomatonMirror.lean` | `Simulation` | σ=1, τ=1 | 0 |

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

[Lean/Edges.lean](../Lean/Edges.lean) contains the registered edges as named typed wrappers; [Lean/EdgeAudit.lean](../Lean/EdgeAudit.lean) prints an audit trail at build time (machines, paper ref, hypothesis list, axiom closure). **Six** edges registered (`EDGE AUDIT: PASS (6 edges)` at build time):

| Edge | Status | Top-level hypotheses | Wrapper axioms |
|---|---|---|---|
| `edge_ECA110_ECA124` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA124_ECA110` | unconditional | (none) | propext, Quot.sound |
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

`Lean/SimulationEncoding.lean` defines four templates:

| Structure | Fields | Use |
|---|---|---|
| `Simulation A B` | `encode`, `commutes`, `halting` | Step-level strict-equality simulation (4 edges) |
| `SimulationViaDecode A B` | `encode`, `decode`, `normalize`, `roundtrip`, `commutes`, `halting` | Decode-based commutes modulo `normalize` (TM→GS) |
| `HaltingSimulation A B` | `encode`, `preserves_halting` | Halting preservation only (e.g. Smith) |
| `SimulationEncoding A B` | `encode`, `decode`, `roundtrip`, `commutes` | Full encoding with decode (currently unused) |

`Simulation` composes via `Simulation.compose` and derives `halting_preserved`. `HaltingSimulation` composes via `HaltingSimulation.compose`.

The "agreed" template form is the decode-based commutes `B.step b ≃ (A.iterationStep n (encode b)).bind decode`. A future refactor should consolidate around a single `Simulation` carrying `encode + decode + roundtrip + commutes + halting`. The `stepNormalized` helpers added to `GeneralizedShift/Defs.lean` and `BiInfiniteTuringMachine/Defs.lean` are the substrate for that future unification (they post-strip trailing zeros so encoded configs land in a canonical, image-preserving subset).

## Current focus

GS → TM general width: all building blocks fully proved (readScan, lastRead, writeLoop, writeZeroShift — 0 sorry). One sorry remains in `fullSim_general` — the composition that chains the 4 phases via `exactSteps_append`. See `Wiki/Plans/GStoTM_GeneralWidth.md`.

Template unification (single `Simulation` template, decode-based form) is on the roadmap but blocked on a non-trivial decode/roundtrip proof for Tag → CTS (one-hot block parser + injectivity lemma). The `stepNormalized` helpers landed in this session as the foundation; the migration of the 4 existing simulations is deferred.

## See also

- [CockeMinskyChain](Proofs/CockeMinskyChain.md) — the full TM → Tag → CTS → (2,3) TM chain
- [SimulationEncoding](Concepts/SimulationEncoding.md) — the core Lean abstraction
- [ProofIntegrity](Concepts/ProofIntegrity.md) — trust model and verification procedures
