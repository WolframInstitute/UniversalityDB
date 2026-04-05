# Turing Machine

The standard model of computation. A finite-state head reads and writes symbols on a tape, moving left or right at each step. State 0 is the halt state.

## Lean formalization

Two variants are defined:

**One-sided TM** (`Lean/Machines/TuringMachine/Defs.lean`): Used for rule enumeration. `Machine` has numberOfStates, numberOfSymbols, and a transition function. `decodeRule` converts a Wolfram-style rule number to explicit transitions.

**Bi-infinite TM** (`Lean/Machines/BiInfiniteTuringMachine/Defs.lean`): Used for simulation proofs. `Configuration` = (state, left tape, head symbol, right tape). Includes `evaluate` (with fuel), `exactSteps`, and `Halts`. Wolfram's (2,3) UTM is defined here as `wolfram23`.

## Universality edges

- TM → Generalized Shift (Moore Thm 7, σ=1, τ=1) — see [TMtoGS](../Proofs/TMtoGS.md)
- GS → TM (Moore Thm 8, σ=1, τ≤2(w-1)+m) — see [GStoTM](../Proofs/GStoTM.md)
- TM → 2-Tag System (Cocke-Minsky 1964) — see [CockeMinskyChain](../Proofs/CockeMinskyChain.md)

## See also

- [GeneralizedShift](GeneralizedShift.md) — dynamical systems equivalent
- [TagSystem](TagSystem.md) — intermediate in the Cocke-Minsky chain
- [Moore1991](../Resources/Moore1991.md) — the GS equivalence paper
