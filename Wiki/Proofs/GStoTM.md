# GS → Turing Machine (Moore Theorem 8)

Any generalized shift can be simulated by a bi-infinite Turing machine with σ=1, τ≤2(w-1)+m where w is the window width and m is the maximum shift magnitude.

## Encoding

The TM executes in three phases per GS step:
1. **Read phase** (w-1 steps): scan right, accumulate window contents in state encoding
2. **Write phase** (w-1 steps): write replacement symbols right-to-left
3. **Shift phase** (≤m steps): move head to match GS shift

TM states encode (phase, position, accumulated data) as a single natural number using base-n arithmetic.

## Lean formalization

`Lean/Proofs/GeneralizedShiftToTuringMachine.lean`

Key definitions: `GSParams`, `TMPhase` (inductive state type: halt/start/read/write/shift), `phaseTransition` (pattern-matching transition), `natToPhase`/`phaseToNat` (Nat encoding roundtrip), `buildTransition` (dispatches through `natToPhase` → `phaseTransition` → `phaseToNat`), `toBiTM`, `encodeConfig`/`decodeConfig`.

Key theorems:
- `decodeWindow_encodeWindow` — window encoding roundtrip
- `decodeConfig_encodeConfig` — config roundtrip
- `natToPhase_shiftState` — Nat→TMPhase roundtrip for shift states
- `buildTransition_shiftState` — transition at shift states produces correct rule
- `shiftPhase_correct` — shift phase: (remaining+1) TM steps = shiftBy (remaining+1)
- `fullSim_w1` — full simulation for windowWidth=1 (first step + shift phase)
- `stepSimulation_w1` — step simulation for windowWidth=1

**Status:** 0 sorry. Step simulation fully proved for windowWidth=1 with formal overhead bound `n ≤ temporalOverhead params`. The `TMPhase` inductive type replaced the original Nat-encoded state arithmetic, making the transition function amenable to pattern-matching proofs. Extending to general w requires handling the multi-step read/write phases (all infrastructure is in place).

## See also

- [TMtoGS](TMtoGS.md) — the forward direction (Moore Theorem 7)
- [TuringMachine](../Systems/TuringMachine.md), [GeneralizedShift](../Systems/GeneralizedShift.md) — the systems
- [Moore1991](../Resources/Moore1991.md) — the paper
