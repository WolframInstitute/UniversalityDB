# ECA Rule 110 ↔ Rule 124 — Proof Skeleton

This is a *demonstration* skeleton showing the new layered format described in [VerificationFramework](../../Plans/VerificationFramework.md). The actual content is folklore (mirror symmetry of ECA rules; cf. Wolfram, [*A New Kind of Science*, Chapter 3](https://www.wolframscience.com/nks/chap-3--the-world-of-simple-programs/), p. 55) and the proof is short, so the skeleton is correspondingly small. Paper-based proofs (Moore 1991, Cook 2004, Cocke-Minsky 1964) will produce richer skeletons.

## Edge claim

Two registered edges in the universality graph (see [Lean/Edges.lean](../../../Lean/Edges.lean)):

| Lean wrapper | Source | Target | Status |
|---|---|---|---|
| `UniversalityGraph.edge_ECA110_ECA124` | Rule 110 on `Fin n → Fin 2` | Rule 124 on `Fin n → Fin 2` | unconditional |
| `UniversalityGraph.edge_ECA124_ECA110` | Rule 124 on `Fin n → Fin 2` | Rule 110 on `Fin n → Fin 2` | unconditional |

Both parametric in tape length `n` with `n ≥ 3`. No external hypotheses.

## Source

Folklore. The single observation is: for all `a,b,c ∈ {0,1}`,
`rule110(a,b,c) = rule124(c,b,a)`. Tape reversal turns one into the other.

## Basic notions

| Notion | Where it appears |
|---|---|
| Pointwise rule identity | L1 |
| Tape reversal as involution | L2 |
| Index arithmetic on `Fin n` | L3, L4 |
| One-step bisimulation | L5 |
| Iteration to k steps | L6 |

## Lemma DAG

```
   L1 (rule identity)         L2 (reversal involution)
        \                          /
         \                        /
          L3 (right→left under reversal)
          L4 (left→right under reversal)
              \           /
               \         /
                L5 (one-step bisimulation)
                     |
                     |
                L6 (k-step bisimulation)
                     |
                     v
              edges ECA110→124, ECA124→110
```

## Lemma nodes

### L1 — pointwise rule identity

**Statement.** ∀ `a, b, c : Fin 2`, `rule110 a b c = rule124 c b a`.
**Source.** Direct check on 8 inputs.
**Lean.** `ElementaryCellularAutomaton.mirrorProperty` ([source](../../../Lean/Proofs/ElementaryCellularAutomatonKleinGroup.lean#L179-L181)).
**Status.** Proved (`decide` on a finite Boolean table).
**Basic notions.** Pointwise rule identity.

### L2 — reversal involution

**Statement.** Reversing a tape twice yields the original tape (for `n ≥ 1`).
**Source.** Index arithmetic.
**Lean.** `ElementaryCellularAutomaton.reverseTapeInvolutive`.
**Status.** Proved.
**Basic notions.** Tape reversal as involution.

### L3 — right neighbor under reversal

**Statement.** `(n - 1 - ((i+1) mod n)) mod n = ((n-1-i) mod n + n - 1) mod n` (for `n ≥ 3`, `i < n`).
**Lean.** `reverseRightIsLeft` (private).
**Status.** Proved.
**Basic notions.** Index arithmetic on `Fin n`.

### L4 — left neighbor under reversal

**Statement.** `(n - 1 - ((i+n-1) mod n)) mod n = ((n-1-i) mod n + 1) mod n`.
**Lean.** `reverseLeftIsRight` (private).
**Status.** Proved.

### L5 — one-step bisimulation

**Statement.** `step rule110 n (reverseTape n tape) = reverseTape n (step rule124 n tape)` for `n ≥ 3`.
**Depends on.** L1, L3, L4.
**Lean.** `ElementaryCellularAutomaton.mirrorSimulationGeneral`.
**Status.** Proved.
**Basic notions.** One-step bisimulation.

### L6 — k-step bisimulation

**Statement.** `iterate rule110 n (reverseTape n tape) k = reverseTape n (iterate rule124 n tape k)`.
**Depends on.** L5, L2.
**Lean.** `ElementaryCellularAutomaton.mirrorSimulationSteps`.
**Status.** Proved.
**Basic notions.** Iteration to k steps.

### Edge assembly

`rule110SimulatesRule124` and `rule124SimulatesRule110` package L5 + a vacuous halting clause (ECA never halts) into the `Simulation` template. Re-exported as `edge_ECA110_ECA124` / `edge_ECA124_ECA110` in [Lean/Edges.lean](../../../Lean/Edges.lean).

## See also

- [ECAMirror](../ECAMirror.md) — informal overview
- [VerificationFramework](../../Plans/VerificationFramework.md) — the framework this skeleton illustrates
- [ProofIntegrity](../../Concepts/ProofIntegrity.md) — trust model
