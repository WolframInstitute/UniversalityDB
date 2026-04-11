# Project Status

Last updated: 2026-04-11

## Generic simulation framework

All simulation proofs use a unified template (`Simulation` / `HaltingSimulation`) defined in `Lean/SimulationEncoding.lean`. Each proof file follows the same pattern: standalone lemmas for `encode`, `commutes`, `halting`, then a trivial assembly into the `Simulation` structure. The type checker guarantees correctness of the simulation statement.

Every machine family has a `toComputationalMachine` wrapper in its `Defs.lean`, enabling uniform simulation statements across all pairs.

## Proved edges

| Edge | File | Template | Overhead | Sorry |
|---|---|---|---|---|
| TM → GS (Moore Thm 7) | `Lean/Proofs/TuringMachineToGeneralizedShift.lean` | `Simulation` | σ=1, τ=1 | 0 (hypotheses for empty-tape configs, well-formedness) |
| GS → TM (Moore Thm 8) | `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | `Simulation` | σ=1, τ≤2(w-1)+m | 1 (fullSim_general for w≥2) |
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

## Machine families in Lean

Each family has a `toComputationalMachine` wrapper and an `iterationStep_eq_exactSteps` compatibility lemma.

- Turing Machine (one-sided): `Lean/Machines/TuringMachine/Defs.lean`
- Bi-infinite Turing Machine: `Lean/Machines/BiInfiniteTuringMachine/Defs.lean`
- Generalized Shift: `Lean/Machines/GeneralizedShift/Defs.lean`
- 2-Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Cyclic Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Elementary Cellular Automaton: `Lean/Machines/ElementaryCellularAutomaton/Defs.lean`

## Simulation framework

`Lean/SimulationEncoding.lean` defines three levels:

| Structure | Fields | Use |
|---|---|---|
| `Simulation A B` | `encode`, `commutes`, `halting` | Step-level simulation with halting preservation |
| `HaltingSimulation A B` | `encode`, `preserves_halting` | Halting preservation only (e.g. Smith) |
| `SimulationEncoding A B` | `encode`, `decode`, `roundtrip`, `commutes` | Full encoding with decode (original, not yet instantiated) |

`Simulation` composes via `Simulation.compose` and derives `halting_preserved`. `HaltingSimulation` composes via `HaltingSimulation.compose`.

## Current focus

GS → TM general width: all building blocks fully proved (readScan, lastRead, writeLoop, writeZeroShift — 0 sorry). One sorry remains in `fullSim_general` — the composition that chains the 4 phases via `exactSteps_append`. See `Wiki/Plans/GStoTM_GeneralWidth.md`.

## See also

- [CockeMinskyChain](Proofs/CockeMinskyChain.md) — the full TM → Tag → CTS → (2,3) TM chain
- [SimulationEncoding](Concepts/SimulationEncoding.md) — the core Lean abstraction
