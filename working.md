# Working Notes: TM ↔ GS Formalization

## Summary (2026-04-05)

Build succeeds with **1 sorry** (GS→TM `stepSimulation_w1` active case).

### TM → GS (Theorem 7) — sorry-free ✅

`Proofs/TuringMachineToGeneralizedShift.lean`

**All proved:**
- Alphabet encoding roundtrip (`decodeActiveEncodeActive`)
- Config encoding roundtrip (`decodeEncode`, nonempty tapes)
- Step commutation (`stepCommutes`, nonempty tapes)
- Halting preservation (`encodedHaltedIsGSHalted`, `mooreHaltingForward`)
- Tape normalization (`headD_normalize`, `tail_normalize`, derived lemmas)
- Step commutation for all configs (`stepCommutesNorm`, with nonempty tape precondition)

### GS → TM (Theorem 8) — 1 sorry

`Proofs/GeneralizedShiftToTuringMachine.lean`

**All proved:**
- Window encoding roundtrip (`decodeWindow_encodeWindow`, via snoc induction)
- Config encoding roundtrip (`decodeConfig_encodeConfig`)
- Helper arithmetic (`foldl_encode_shift`, `encodeWindow_cons/snoc`, `mul_add_div/mod_right`)

**Sorry'd (1):**
- `stepSimulation_w1` active case — proving TM execution matches GS step

**Construction (computationally verified, no sorry):**
- `buildTransition` — 3-phase TM (read/write/shift), 85 lines
- `StepSimulation` spec with `shiftMagnitude ≥ 1` precondition
- Verified on windowWidth=1 and windowWidth=3 examples

## Remaining work: step simulation proof

### What needs to be proved

The last sorry requires showing that `buildTransition` produces TM steps that compose to match `GeneralizedShift.shiftBy`. This should be proved for general window widths, not just w=1.

The overhead bound (`n ≤ temporalOverhead`) is the easy part — just counting steps. The hard part is proving the simulation is correct at all: that the TM starting from `encodeConfig gsConfig` reaches `encodeConfig gsConfig'` in ANY number of steps.

### Why it's hard

`buildTransition` is an 85-line function with 5 state-range branches (halt, state 1, read phase, write phase, shift phase). Proving the simulation requires:

1. **Shift phase lemma** (induction on remaining count): Show that `shiftState params k goLeft` executes k+1 TM steps, each moving the head without modifying the tape, ending in state 1. This corresponds to `GeneralizedShift.shiftBy`. Needs arithmetic: `shiftState` encodes `(remaining, goLeft)` as a single Nat, and `buildTransition` must decode it correctly via `/2` and `%2`.

2. **Write phase lemma** (induction on position): Show that `writeState params pos windowCode` writes `replacement[pos]` and moves left, iterating from pos=w-2 down to pos=0, then calls `startShift`. Needs: `writeState` encodes `(pos, windowCode)`, and `buildTransition` decodes via `/nPow` and `%nPow`.

3. **Read phase lemma** (induction on position): Show that `readState params pos partialCode` reads the tape cell, accumulates it in the state, and moves right, iterating from pos=1 to pos=w-1, then transitions to write phase. Needs same encoding/decoding arithmetic.

4. **Combining**: Compose read (w-1 steps) + write (w-1 steps) + shift (m steps) = 2(w-1)+m steps total.

Each phase lemma requires proving `buildTransition` produces the right `TransitionRule` for the corresponding state range. This means navigating through the if/else branches and showing the arithmetic encoding/decoding is correct.

### Suggested approach

1. Prove `buildTransition` extraction lemmas for each state range (what transition rule it produces)
2. Prove each phase separately by induction
3. Combine phases for the full `StepSimulation`

### Key design decisions made

1. **GS always moves:** `shiftMagnitude ≥ 1` for all active windows (precondition on `StepSimulation`)
2. **Tape normalization:** `normalize` strips trailing far-end zeros; `headD_normalize`/`tail_normalize` are the key lemmas
3. **Nonempty tape precondition:** `stepCommutesNorm` requires nonempty tapes, delegating to `stepCommutes`
4. **Window roundtrip via snoc induction:** `dropLast_append_getLast` proved manually (no `List.reverseRecOn` in Lean 4 core)

### Lean proof patterns discovered

- Use `if_pos`/`if_neg` with hypothesis for `if`/`match` reduction, not `simp`
- Structure equality: `simp only [Configuration.mk.injEq]` then `refine ⟨..⟩`
- Bool conditions: `by_cases h : expr = true`
- Nat div/mod with reversed multiplication: proved `mul_add_div_right`/`mul_add_mod_right` helpers
