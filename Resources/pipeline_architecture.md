# LLM Pipeline Architecture

## Overview

The pipeline iteratively expands the Universality Graph through four operations,
each using an LLM (Claude / GPT-4 class) with the Wolfram Language as computational
backend and Lean 4 as the verification layer.

```
┌─────────────────────────────────────────────────────┐
│                  Universality Graph                   │
│              (Lean project + JSON export)              │
└────────────┬──────────────┬──────────────┬────────────┘
             │              │              │
        ┌────▼────┐   ┌────▼────┐   ┌────▼────┐
        │ Adjoin  │   │ Adjoin  │   │ Compose │
        │ Vertex  │   │  Edge   │   │  Edges  │
        └────┬────┘   └────┬────┘   └────┬────┘
             │              │              │
        ┌────▼──────────────▼──────────────▼────┐
        │          LLM (Claude / GPT-4)          │
        │   Generates Lean code + proof sketches │
        └────────────────┬───────────────────────┘
                         │
                  ┌──────▼──────┐
                  │   Wolfram   │
                  │  Language   │
                  │ Pre-check   │
                  └──────┬──────┘
                         │
                  ┌──────▼──────┐
                  │   Lean 4    │
                  │ Type-check  │
                  └──────┬──────┘
                         │
                    ┌────▼────┐
                    │ Accept  │──── if Lean accepts ───▶ Add to graph
                    │ Reject  │──── if Lean rejects ───▶ Feed error to LLM, retry
                    └─────────┘
```


## Operation 1: Adjoin Vertex

**Input:** An existing machine family in the graph (e.g., elementary CAs).
**LLM prompt:** "Here is the Lean definition of Rule 110 (an elementary CA).
Generate the Lean definition for Rule 124, Rule 137, and Rule 193 — other
elementary CAs that exhibit Class 4 behavior."
**Output:** New `def` declarations with concrete transition tables.
**Validation:** Lean type-checks the definition. Wolfram Language runs the CA
for 1000 steps to verify Class 4 behavior (visual/statistical check).


## Operation 2: Adjoin Edge (Simulation Proof)

**Input:** Two systems A and B in the graph, no existing edge A → B.
**LLM prompt:** (multi-stage)

### Stage 2a: Encoding Proposal
"System A is [Lean definition]. System B is [Lean definition].
Propose an encoding function `encode : B.Config → A.Config` that would allow
A to simulate B. Explain the encoding strategy."

### Stage 2b: Wolfram Pre-validation
Take the proposed encoding, implement it in Wolfram Language, and run:
- 100 random B-configurations
- Encode each into A
- Run A for k steps (where k is the proposed step ratio)
- Decode and check against one step of B
- If >95% match, proceed. If not, feed mismatches back to LLM.

### Stage 2c: Lean Proof Generation
"Here is the encoding function that passed pre-validation. Generate a Lean
proof that this encoding constitutes a valid Simulation A B, including the
roundtrip and commutativity lemmas."

### Stage 2d: Lean Verification
Submit to Lean type-checker. If it fails:
- Extract the error message
- Feed it back to the LLM with context
- Retry (up to N times)

**Output:** A `Simulation A B` term in Lean, plus overhead bounds.


## Operation 3: Compose Edges

**Input:** A path A → B → C in the graph (two existing edges).
**LLM prompt:** Not needed — composition is automatic via `Simulation.compose`.
**Wolfram pre-check:** Verify that the composed overhead matches prediction.
**Output:** A new edge A → C with composed overhead.

This is the cheapest operation — it's purely mechanical. But it's important because:
- It fills in transitive edges
- It may reveal that a composed path has lower overhead than a direct edge
- It makes the graph denser, aiding future LLM proofs


## Operation 4: Compile Across Formalisms

**Input:** A machine in one formalism (e.g., a TM) and a target formalism (e.g., CA).
**LLM prompt:** "Translate this 3-state 2-color TM into an equivalent cellular
automaton. What is the minimum number of colors needed? Generate both the CA
definition and the simulation proof."
**Output:** A new vertex (the compiled CA) + an edge (TM → CA simulation).


## Retry Logic and LLM Management

- **Max retries per edge:** 10 attempts with error feedback
- **Temperature scheduling:** Start at low temperature (0.2) for the first attempt,
  increase to 0.8 on later retries to encourage diversity
- **Prompt caching:** Cache successful proof patterns as few-shot examples
- **Difficulty estimation:** Track success rate per (source_family, target_family)
  pair to prioritize easier edges first
- **Parallel exploration:** Run multiple LLM instances on different candidate edges


## Wolfram Language Backend

The Wolfram Language serves three roles:

1. **Machine exploration:** Enumerate machines by parameter, classify behavior
   (Wolfram Classes 1–4), identify universality candidates.

2. **Encoding construction:** Computationally build candidate encodings by:
   - Running both systems on test inputs
   - Searching for patterns in the correspondence
   - Constructing lookup tables for local rules

3. **Pre-validation:** Before expensive Lean proof attempts, check:
   - Does the encoding produce valid configurations?
   - Does the step correspondence hold on test cases?
   - What is the empirical step ratio?
   - Are there obvious failure modes?

This dramatically reduces wasted Lean compilation time.


## Output Format

Each successful proof is registered in:
1. **Lean project:** A `.lean` file added to the project, building on Mathlib
2. **JSON export:** Machine-readable graph data with all metadata
3. **Human summary:** Auto-generated natural language description of the proof

The JSON export supports graph visualization and analysis tools.
