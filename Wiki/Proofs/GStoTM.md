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

Key definitions: `GSParams`, `readState`/`writeState`/`shiftState` (state encoders), `buildTransition` (85-line transition constructor), `toBiTM`, `encodeConfig`/`decodeConfig`.

Key theorems:
- `decodeWindow_encodeWindow` — window encoding roundtrip
- `decodeConfig_encodeConfig` — config roundtrip
- `stepSimulation_w1` — step simulation for windowWidth=1

**Status:** 1 sorry in `stepSimulation_w1` active case. The difficulty is proving that `buildTransition` produces correct phase compositions for general window widths. See `working.md` for detailed analysis.

## See also

- [[TMtoGS]] — the forward direction (Moore Theorem 7)
- [[TuringMachine]], [[GeneralizedShift]] — the systems
- [[Moore1991]] — the paper
