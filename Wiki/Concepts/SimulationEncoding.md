# Simulation Encoding

A simulation of machine B by machine A. Three layers, in increasing strength, all defined in [Lean/SimulationEncoding.lean](../../Lean/SimulationEncoding.lean):

## 1. `HaltingSimulation` — weakest

```
structure HaltingSimulation (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  preserves_halting : ∀ b, B.Halts b → A.Halts (encode b)
```

Only halting preservation. Used when no step correspondence is available (e.g. Smith CTS → (2,3) TM).

## 2. `Simulation` — canonical, composable

```
structure Simulation (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  commutes : ∀ b b', B.step b = some b' →
    ∃ n, A.iterationStep n (encode b) = some (encode b')
  halting : ∀ b, B.step b = none → A.Halts (encode b)
```

No decode required. The default for most edges. Composes (`Simulation.compose`) and gives halting preservation (`Simulation.halting_preserved`). Used by every edge except TM → GS.

## 3. `SimulationEncoding` — conjugation form

```
structure SimulationEncoding (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  decode : A.Configuration → Option B.Configuration
  commutes : ∀ b b', B.step b = some b' →
    ∃ n a, A.iterationStep n (encode b) = some a ∧ decode a = some b'
  halting : ∀ b, B.step b = none → A.Halts (encode b)
```

Reads as `step_B(b) = decode (step_A^n (encode b))`: one B-step lifts to some n A-steps, after which decoding recovers `b'`. For edges with a natural decode (currently TM → GS and GS → TM, Moore Theorems 7 and 8).

**No roundtrip field, no normalize field.** Canonicalization, when needed, is on the *machine* via `stepNormalized` plus a bisimulation lemma (e.g. [BiInfiniteTuringMachine.step_stripConfig_bisim](../../Lean/Machines/BiInfiniteTuringMachine/Defs.lean) at line 242), not as a structure field.

This is purely a presentation form. Composition flows through `Simulation`.

## How papers fit

| Paper | Theorem | Layer |
|---|---|---|
| ECA 110 ↔ 124 (folklore) | `step_124 = reverse ∘ step_110 ∘ reverse` | `Simulation`, σ=τ=1 |
| Moore 1991, Thm 7 | TM ↔ GS conjugacy | `SimulationEncoding`, σ=τ=1 |
| Moore 1991, Thm 8 | GS → TM, τ = 2(w−1)+m | `SimulationEncoding`, σ=1 |
| Cook 2004 | Tag → CTS, τ = 2k | `Simulation`, fixed n=2k |
| Cocke-Minsky 1964 | TM → 2-tag | `Simulation`, existential n |
| Smith 2007 | CTS → (2,3) TM | `HaltingSimulation` (paper is contested) |

## See also

- [ComputationalMachine](ComputationalMachine.md) — the vertex type
- [Overhead](Overhead.md) — quantifying simulation cost
- [CockeMinskyChain](../Proofs/CockeMinskyChain.md) — composition in action
- [TMtoGS](../Proofs/TMtoGS.md) — the TM ↔ GS edge using `SimulationEncoding`
