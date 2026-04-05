# Project Status

> Status: **draft**

Last updated: 2026-04-05

## Proved edges (0 sorry)

| Edge | File | Overhead |
|---|---|---|
| Tag → CyclicTag | `Lean/Proofs/TagSystemToCyclicTagSystem.lean` | 1 tag step = 2k CTS steps |
| ECA Rule 110 ↔ Rule 124 | `Lean/Proofs/ElementaryCellularAutomatonMirror.lean` | σ=1, τ=1 (tape reversal) |

## Partially proved edges

| Edge | File | Status |
|---|---|---|
| TM → GS (Moore Thm 7) | `Lean/Proofs/TuringMachineToGeneralizedShift.lean` | Roundtrips proved, step commutation proved for nonempty tapes, halting forward proved. 0 sorry. |
| GS → TM (Moore Thm 8) | `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | Window roundtrip proved, config roundtrip proved. 1 sorry in `stepSimulation_w1` active case. |

## Hypothetical edges (stated as axioms)

| Edge | File | Status |
|---|---|---|
| TM → 2-Tag (Cocke-Minsky) | `Lean/Proofs/CockeMinsky.lean` | `CockeMinskyStepSimulation` is a hypothesis. Halting correspondence proved assuming it. |
| CTS → (2,3) TM (Smith) | `Lean/Proofs/CockeMinsky.lean` | `SmithSimulation` is a hypothesis. |

## Main theorem

`wolfram23Universal` in `Lean/Proofs/CockeMinsky.lean`: Wolfram's (2,3) TM is universal, assuming CockeMinsky and Smith simulation properties.

## Machine families in Lean

- Turing Machine (one-sided): `Lean/Machines/TuringMachine/Defs.lean`
- Bi-infinite Turing Machine: `Lean/Machines/BiInfiniteTuringMachine/Defs.lean`
- Generalized Shift: `Lean/Machines/GeneralizedShift/Defs.lean`
- 2-Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Cyclic Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Elementary Cellular Automaton: `Lean/Machines/ElementaryCellularAutomaton/Defs.lean`

## Current focus

Closing the last sorry in GS → TM (`stepSimulation_w1` active case). See `working.md` for detailed analysis.

## See also

- [[CockeMinskyChain]] — the full TM → Tag → CTS → (2,3) TM chain
- [[SimulationEncoding]] — the core Lean abstraction
