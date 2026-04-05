# Computational Machine

The base abstraction in the universality graph. A computational machine is a pair of a configuration type and a step function that either returns a new configuration or halts (returns `none`).

## Lean definition

`Lean/ComputationalMachine.lean`

```
structure ComputationalMachine where
  Configuration : Type
  step : Configuration → Option Configuration
```

Key derived notions:
- `iterationStep n config` — run n steps
- `Halts config` — ∃n such that iterationStep n config = none

All machine families (TM, GS, Tag, CTS, ECA) are instances of this.

## See also

- [SimulationEncoding](SimulationEncoding.md) — morphisms between machines
- [Overhead](Overhead.md) — cost of simulation
