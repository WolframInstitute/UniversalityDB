# Pipeline Architecture

The LLM pipeline for automatically expanding the universality graph. Not yet implemented — this is the design document for a future stage.

## Operations

1. **Adjoin Vertex** — generate new machine definitions via LLM, type-check in Lean, validate behavior in Wolfram.
2. **Adjoin Edge** — 4-stage process: encoding proposal → Wolfram pre-validation → Lean proof generation → Lean verification. Up to 10 retries with temperature scheduling.
3. **Compose Edges** — automatic via `SimulationEncoding.compose`. Purely mechanical, fills transitive edges.
4. **Compile Across Formalisms** — translate a machine from one formalism to another (e.g. TM → CA), producing both a new vertex and an edge.

## Architecture

LLM proposes Lean code → Wolfram pre-checks on finite examples → Lean type-checks → accept or retry with error feedback.

## See also

- [[SimulationEncoding]] — what gets produced
- [[Polu2020]], [[Zheng2025]] — LLM theorem proving background
