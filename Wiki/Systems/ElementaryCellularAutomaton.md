# Elementary Cellular Automaton

> Status: **draft**

An elementary cellular automaton (ECA) is a 1D cellular automaton with 2 states and nearest-neighbor interactions. Each of the 256 rules is identified by a Wolfram rule number encoding the 8-entry lookup table.

## Lean formalization

`Lean/Machines/ElementaryCellularAutomaton/Defs.lean`

`ruleTable` converts a rule number + 3-bit neighborhood to an output bit. Built-in rules: `rule110`, `rule124`, `rule137`. `step` applies the rule to a periodic tape (Fin n → Fin 2). `iterate` composes multiple steps.

## Key rules

- **Rule 110**: proved universal by Cook (2004) via CTS simulation. Class 4 behavior.
- **Rule 124**: mirror of Rule 110 (tape reversal bisimulation, σ=1, τ=1). See [[ECAMirror]].

## Universality edges

- ECA Rule 110 ↔ Rule 124 (tape reversal): fully proved. See [[ECAMirror]].
- Rule 110 universality (Cook 2004): not yet formalized directly. See [[Cook2004]].

## See also

- [[Cook2004]] — Rule 110 universality proof
- [[Neary2006]] — polynomial-overhead alternative
