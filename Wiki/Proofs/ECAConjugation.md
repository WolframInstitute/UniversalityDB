# ECA Klein-4 Conjugation Framework

The 256 elementary cellular automata are organized by a Klein-4 group of trivial conjugations. The two generators are:

- **Mirror** — `f(a, b, c) = g(c, b, a)`, encoded by tape reversal.
- **Complement** — `f(a, b, c) = ¬g(¬a, ¬b, ¬c)`, encoded by bit complement.

Both are involutive and they commute, so the orbit of any rule has size 1, 2, or 4. For Rule 110 the orbit is `{110, 124, 137, 193}` and the framework gives all six bidirectional bisimulation edges with σ = 1, τ = 1.

## Encoding

| Edge | Encoding | Constraint |
|---|---|---|
| 110 ↔ 124 (mirror) | `reverseTape n tape (i) = tape ((n-1-i) mod n)` | `n ≥ 3` |
| 110 ↔ 137 (complement) | `complementTape n tape (i) = 1 - tape i` | none |
| 110 ↔ 193 (combined) | `reverseTape n ∘ complementTape n` | `n ≥ 3` |

The `n ≥ 3` constraint comes only from the mirror — index arithmetic on the periodic tape needs three distinct positions to relate `(n-1-(i+1) mod n) mod n` with `((n-1-i) mod n + n - 1) mod n`. The complement is index-preserving and works for any `n`.

## Lean formalization

`Lean/Proofs/ElementaryCellularAutomatonKleinGroup.lean` (generic Klein-4 framework, the generic mirror/complement wrappers, and the Rule 110 orbit specializations).

### Generic, rule-parametric theorems

Defined for any rule, not just Rule 110:

- `mirrorRule`, `complementRule` — rule transforms (each involutive)
- `complementTape`, `mirrorComplementTape` — tape transforms
- `complementSimulationGeneral` — `step (complementRule rule) n (complementTape n tape) = complementTape n (step rule n tape)` (no length constraint)
- `mirrorSimulationGenericGeneral` — analogous identity for `mirrorRule` and `reverseTape` (requires `n ≥ 3`)
- `mirrorComplementSimulation` — composed identity

### Specific Rule 110 orbit identifications (each `decide` over 8 neighbourhoods)

- `mirrorRule_rule110 : mirrorRule rule110 = rule124`
- `complementRule_rule110 : complementRule rule110 = rule137`
- `mirrorRule_rule137 : mirrorRule rule137 = rule193`
- `complementRule_rule124 : complementRule rule124 = rule193`
- Plus derived identities (`complementRule_rule137 = rule110`, `mirrorRule_rule124 = rule110`, …)

### Simulation wrappers

- `mirrorRuleSimulatesRule`, `ruleSimulatesMirrorRule` — generic mirror wrappers (`n ≥ 3`)
- `rule110SimulatesRule137`, `rule137SimulatesRule110` — complement edge (no length constraint)
- `rule110SimulatesRule193`, `rule193SimulatesRule110` — combined edge (`n ≥ 3`)

**Status:** 0 sorry. Axiom closure: `[propext, Quot.sound]`. Registered in `Lean/Edges.lean` as `edge_ECA110_ECA124`, `edge_ECA124_ECA110`, `edge_ECA110_ECA137`, `edge_ECA137_ECA110`, `edge_ECA110_ECA193`, `edge_ECA193_ECA110`.

## Why these are "trivial" symmetries

Mirror and complement are conjugations by a *spatial* tape automorphism (reversal) and a *fibrewise* automorphism of the alphabet (bit flip). Neither does any computational work: it just relabels positions or values. The Klein-4 group acts on the 256 ECA rules and partitions them into orbits — there are 88 inequivalent rules under this action.

These edges are useful for the universality graph: any universality result for one rule in an orbit immediately propagates to the others. Cook's universality of Rule 110 therefore yields universality of Rules 124, 137, 193 by composition.

## See also

- [ElementaryCellularAutomaton](../Systems/ElementaryCellularAutomaton.md) — the system family
- [ECAMirror](ECAMirror.md) — the original Rule 110 ↔ Rule 124 specific proof
- [Cook2004](../Resources/Cook2004.md) — Rule 110 universality proof
- [SimulationEncoding](../Concepts/SimulationEncoding.md) — `Simulation` template used by all four wrappers
