# Working Notes: TM ↔ GS Formalization

## Summary (2026-04-06)

Build succeeds with **1 sorry** in `fullSim_general` (read+write phase loop for w≥2).

- TM → GS: fully proved (0 sorry)
- GS → TM w=1: fully proved (0 sorry)
- GS → TM general w: `stepSimulation` theorem wired, 1 sorry in `fullSim_general`

### TMPhase refactor

Introduced `TMPhase` inductive type (halt/start/read/write/shift). `buildTransition` dispatches through `natToPhase → phaseTransition → phaseToNat`. The Nat encoding roundtrips (`natToPhase_{shift,read,write}State`) are proved.

### What's proved for general w

- `natToPhase_readState`, `natToPhase_writeState` — Nat→TMPhase roundtrips
- `buildTransition_readState`, `buildTransition_writeState` — single-step characterization
- `encodeConfig_shiftBy_flatten` — bridge: w-cell and 1-cell views agree under encodeConfig after shiftBy (requires tape length ≥ mag)
- `shiftPhase_correct` — shift phase by induction (from w=1 proof)
- `fullSim_w1` — w=1 case complete
- `stepSimulation` — general theorem, delegates to w=1 and fullSim_general

### Remaining: fullSim_general (read+write phase loop)

The sorry is in proving that 2(w-1)+mag TM steps from `encodeConfig` match one GS step for w≥2. The proof requires:

1. **Read phase** (w steps): state 1 → readState → ... → writeState. By induction on remaining read steps. At each step, `buildTransition_readState` gives the transition, head moves right, partial code accumulates.

2. **Write phase** (w-1 steps): writeState → ... → startShiftPhase. By induction on write position. At each step, `buildTransition_writeState` gives the transition, replacement symbol written, head moves left.

3. **Shift entry** (1 step within write phase): pos=0 write step calls `startShiftPhase`, which enters shift phase or reaches state 1 (if mag=1).

4. **Shift phase** (mag-1 steps): already proved as `shiftPhase_correct`.

5. **Composition**: chain phases using `exactSteps_succ`, apply `encodeConfig_shiftBy_flatten` bridge.

### Difficulties encountered

- `omega` cannot reason about products of variables (e.g., `pos * nw < w * nw`). Need explicit `Nat.mul_le_mul_right` via `mul_nPow_lt`.
- `simp` with `shiftBy` causes infinite recursion (recursive function). Use `unfold shiftBy` for one step.
- `generalize nPow ... = nw` must be done carefully — residual `writeStateBase`/`shiftStateBase` may still contain `nPow`.
- List `dropLast`/`getLast` on `c :: d :: ds` normalizes to `c :: (d :: ds).dropLast`, requiring manual `hDL`/`hGL` rewrites before applying IH.
- `(c :: xs) ++ ys` vs `c :: (xs ++ ys)` — `List.cons_append` needed for `rw`.

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
