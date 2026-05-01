# ECA Rule 110 ↔ Rule 124 (Tape Reversal)

A bisimulation between elementary cellular automata Rule 110 and Rule 124 via tape reversal. Overhead: σ=1, τ=1.

## Encoding

`reverseTape` reverses the bit order on a periodic tape. The key identity: rule110(a,b,c) = rule124(c,b,a) for all a,b,c in {0,1}.

## Lean formalization

`Lean/Proofs/ElementaryCellularAutomatonKleinGroup.lean`

Key theorems:
- `mirrorProperty` — pointwise rule identity
- `mirrorRuleSimulatesRule`, `ruleSimulatesMirrorRule` — generic mirror bisimulations
- `reverseTapeInvolutive` — double reversal = identity
- `mirrorSimulationGeneral` — one step commutes with reversal
- `mirrorSimulationSteps` — k steps commute with reversal

**Status:** 0 sorry. Fully proved.

## See also

- [ECAConjugation](ECAConjugation.md) — same Klein-group file, viewed as the full symmetry framework
- [ElementaryCellularAutomaton](../Systems/ElementaryCellularAutomaton.md) — the system family
- [Cook2004](../Resources/Cook2004.md) — Rule 110 universality
