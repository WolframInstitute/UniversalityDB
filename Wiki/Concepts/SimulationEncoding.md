# Simulation Encoding

A simulation encoding is a morphism between two computational machines: it certifies that machine A can simulate machine B. This is the edge type in the universality graph.

## Lean definition

`Lean/SimulationEncoding.lean`

```
structure SimulationEncoding (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  decode : A.Configuration → Option B.Configuration
  roundtrip : ∀ config, decode (encode config) = some config
  commutes : ∀ config config', B.step config = some config' →
    ∃n, A.iterationStep n (encode config) = some (encode config')
```

Key properties:
- **Roundtrip**: decoding an encoded config recovers the original.
- **Commutation**: every step of B is matched by some number of steps of A.
- **Identity**: `SimulationEncoding.id`
- **Composition**: `SimulationEncoding.compose` (transitivity — chain simulations)

## See also

- [[ComputationalMachine]] — the vertex type
- [[Overhead]] — quantifying simulation cost
- [[CockeMinskyChain]] — composition in action
