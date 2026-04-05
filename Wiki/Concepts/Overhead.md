# Overhead

> Status: **draft**

Overhead quantifies the cost of a simulation encoding. It has two components: spatial (how much larger the encoded configuration is) and temporal (how many steps of the simulator per step of the simulated system).

## Lean definition

`Lean/SimulationEncoding.lean`

```
structure Overhead where
  spatial : Nat → Nat
  temporal : Nat → Nat
```

Overheads compose: `Overhead.compose` chains spatial and temporal functions. `Overhead.id` is (id, id).

## Examples

| Edge | Spatial | Temporal |
|---|---|---|
| TM → GS (Moore Thm 7) | σ=1 | τ=1 |
| GS → TM (Moore Thm 8) | σ=1 | τ=2(w-1)+m |
| Tag → CTS (Cook) | one-hot (×k) | 2k steps per tag step |
| ECA 110 ↔ 124 | σ=1 | τ=1 |

## See also

- [[SimulationEncoding]] — the structure carrying overhead
- [[ComputationalMachine]] — what's being measured
