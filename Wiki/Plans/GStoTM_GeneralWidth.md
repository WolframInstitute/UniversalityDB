# Plan: GS→TM General Window Width

## Goal

Extend `stepSimulation_w1` (windowWidth=1) to a general `stepSimulation` theorem for all window widths.

## Steps

- [x] Shift phase: `shiftPhase_correct` (proved)
- [x] Arithmetic: `nPow_pos`, `encodeWindow_bound`, `mul_nPow_lt`, `exactSteps_succ/none`
- [x] natToPhase roundtrips: `natToPhase_readState`, `natToPhase_writeState` (proved, pattern: unfold → generalize nPow → simp → split chain with omega)
- [x] buildTransition lemmas: `buildTransition_readState`, `buildTransition_writeState` (proved, trivial via natToPhase + phaseTransition)
- [x] General `stepSimulation` wired to `fullSim_general` via `fullSim_w1` (w=1) and sorry (w≥2)
- [ ] `fullSim_general`: read + write + shift phases for w ≥ 2 — **the remaining sorry**

### What fullSim_general needs
1. Unfold first step: state 1 → readState 1 c₀ (uses buildTransition + phaseTransition)
2. Read loop: readState pos partial → readState (pos+1) newPartial, induction on (w-1-pos)
3. Last read step enters write phase: readState (w-1) partial → writeState (w-2) fullCode
4. Write loop: writeState pos code → writeState (pos-1) code, induction on pos
5. Last write step (pos=0): startShiftPhase → shift phase or state 1
6. Shift phase: already proved as shiftPhase_correct
7. Bridge: relate shiftBy on w-cell config to the 1-cell configs produced by the TM

### Difficulties
- Each read/write step produces a different tape layout (list cons/append)
- omega cannot reason about products of variables — need explicit Nat.mul_le_mul_right
- encodeConfig match on cells needs case splits

## Key decisions

- **Tape-length precondition**: `left.length ≥ maxShift ∧ right.length ≥ maxShift` to avoid 0-padding mismatch between GS shiftBy and TM shift phase (both pad with 0 but produce structurally different lists)
- **New hypotheses**: `hAlpha` (alphabetSize≥1), `hBound` (replacement values < alphabetSize), `hCellBound` (cell values < alphabetSize)
- **TMPhase architecture reused**: same natToPhase/phaseToNat pattern for read/write as for shift

## History

| Date | Actor | Action |
|---|---|---|
| 2026-04-06 | LLM | Created plan based on architecture analysis |
| 2026-04-06 | LLM | Proved arithmetic helpers, natToPhase roundtrips for read/write, buildTransition lemmas. General theorem wired with 1 sorry in fullSim_general. |
