# ECA Rule 110 ↔ Rule 124 (Tape Reversal)

A bisimulation between elementary cellular automata Rule 110 and Rule 124 via tape reversal. Overhead: σ=1, τ=1.

## Encoding

`reverseTape` reverses the bit order on a periodic tape. The key identity: rule110(a,b,c) = rule124(c,b,a) for all a,b,c in {0,1}.

## Lean formalization

`Lean/Proofs/ElementaryCellularAutomatonMirror.lean`

Key theorems:
- `mirrorProperty` — pointwise rule identity
- `reverseTapeInvolutive` — double reversal = identity
- `mirrorSimulationGeneral` — one step commutes with reversal
- `mirrorSimulationSteps` — k steps commute with reversal

**Status:** 0 sorry. Fully proved.

## See also

- [ECAConjugation](ECAConjugation.md) — Klein-4 framework generalising this proof to complement and combined symmetries
- [ElementaryCellularAutomaton](../Systems/ElementaryCellularAutomaton.md) — the system family
- [Cook2004](../Resources/Cook2004.md) — Rule 110 universality
