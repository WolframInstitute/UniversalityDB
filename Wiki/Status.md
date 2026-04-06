# Project Status

Last updated: 2026-04-06

## Proved edges (0 sorry)

| Edge | File | Overhead |
|---|---|---|
| TM → GS (Moore Thm 7) | `Lean/Proofs/TuringMachineToGeneralizedShift.lean` | σ=1, τ=1 |
| GS → TM (Moore Thm 8) | `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | σ=1, τ≤2(w-1)+m (bound proved, simulation proved for w=1) |
| Tag → CyclicTag | `Lean/Proofs/TagSystemToCyclicTagSystem.lean` | 1 tag step = 2k CTS steps |
| ECA Rule 110 ↔ Rule 124 | `Lean/Proofs/ElementaryCellularAutomatonMirror.lean` | σ=1, τ=1 (tape reversal) |

## Partially proved edges

*None currently.*

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

## Overhead formalization

Overhead bounds are proved per-edge as standalone theorems but **not yet bundled** into `Overhead` records or `SimulationEncoding` instances. Packaging them would enable formal composition via `Overhead.compose`.

## Current focus

GS → TM sorry closed (2026-04-06). Next: extend `stepSimulation_w1` to general window widths, bundle proofs into `SimulationEncoding` instances, or pick a new edge from `Wiki/Plans/NextEdges.md`.

## See also

- [CockeMinskyChain](Proofs/CockeMinskyChain.md) — the full TM → Tag → CTS → (2,3) TM chain
- [SimulationEncoding](Concepts/SimulationEncoding.md) — the core Lean abstraction
