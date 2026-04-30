# Elementary Cellular Automaton

An elementary cellular automaton (ECA) is a 1D cellular automaton with 2 states and nearest-neighbor interactions. Each of the 256 rules is identified by a Wolfram rule number encoding the 8-entry lookup table.

## Lean formalization

`Lean/Machines/ElementaryCellularAutomaton/Defs.lean`

`ruleTable` converts a rule number + 3-bit neighborhood to an output bit. Built-in rules: `rule110`, `rule124`, `rule137`, `rule193`. `step` applies the rule to a periodic tape (Fin n → Fin 2). `iterate` composes multiple steps.

## Key rules

- **Rule 110**: proved universal by Cook (2004) via CTS simulation. Class 4 behavior.
- **Rules 124, 137, 193**: Klein-4 conjugates of Rule 110.
  - Rule 124 = mirror(110)
  - Rule 137 = complement(110)
  - Rule 193 = mirror(complement(110))

  All three inherit universality from Rule 110 via bisimulations with σ = 1, τ = 1. See [ECAConjugation](../Proofs/ECAConjugation.md).

## Universality edges

- Rule 110 ↔ Rule 124 (tape reversal): fully proved. See [ECAMirror](../Proofs/ECAMirror.md).
- Rule 110 ↔ Rule 137 (bit complement): fully proved. See [ECAConjugation](../Proofs/ECAConjugation.md).
- Rule 110 ↔ Rule 193 (reversal + complement): fully proved. See [ECAConjugation](../Proofs/ECAConjugation.md).
- Rule 110 universality (Cook 2004): not yet formalized directly. See [Cook2004](../Resources/Cook2004.md).

## See also

- [ECAMirror](../Proofs/ECAMirror.md) — Rule 110 ↔ Rule 124 specific proof
- [ECAConjugation](../Proofs/ECAConjugation.md) — Klein-4 framework (mirror, complement, combined)
- [Cook2004](../Resources/Cook2004.md) — Rule 110 universality proof
- [Neary2006](../Resources/Neary2006.md) — polynomial-overhead alternative
