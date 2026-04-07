# Plan: GS→TM General Window Width

## Goal

Extend `stepSimulation_w1` (windowWidth=1) to a general `stepSimulation` theorem for all window widths.

## Steps

- [x] Shift phase: `shiftPhase_correct` (proved)
- [x] Arithmetic: `nPow_pos`, `encodeWindow_bound`, `mul_nPow_lt`, `exactSteps_succ/none`
- [x] natToPhase roundtrips: `natToPhase_readState`, `natToPhase_writeState` (proved, pattern: unfold → generalize nPow → simp → split chain with omega)
- [x] buildTransition lemmas: `buildTransition_readState`, `buildTransition_writeState` (proved, trivial via natToPhase + phaseTransition)
- [x] General `stepSimulation` wired to `fullSim_general` via `fullSim_w1` (w=1) and sorry (w≥2)
- [x] `exactSteps_append`: composition lemma for step sequences
- [x] `nPow_mono`, `code_step_bound`: arithmetic helpers for code bounds
- [x] `biTM_step_start_w2`, `biTM_step_readMid`: single read-step lemmas
- [x] `readMidLoop`: read loop by induction on cells (code < nPow n pos bound)
- [x] `readScan`: combined start + read loop (w-1 steps from state 1)
- [x] `biTM_step_lastRead`: last read step entering write phase
- [x] `biTM_step_writeMid`: single intermediate write step
- [x] `writeLoop`: fully proved (fixed replPrefix→replAsc ordering, added getLastD_cons helper)
- [x] `writeZeroShift`: write-0 step + shift phase, fully proved (4 cases: dir × mag)
- [ ] `fullSim_general`: composition of readScan + lastRead + writeLoop + writeZeroShift + bridge — **1 sorry**

### What remains for fullSim_general
All building blocks are proved. The **one remaining sorry** is the composition — chaining them via `exactSteps_append`:
1. Split cells = c₀ :: init ++ [last] (use `dropLast_append_getLast`) ← done in proof
2. Apply `readScan` for w-1 steps → readState(w-1, encodeWindow n (c₀::init))
3. Apply `biTM_step_lastRead` for 1 step → writeState(w-2, fullCode)
4. Apply `writeLoop` for w-2 steps → writeState(0, fullCode) (skip for w=2)
5. Apply `writeZeroShift` for mag steps → encodeConfig(shiftBy {left, [r₀], right'} mag dir)
6. Apply `encodeConfig_shiftBy_flatten` to bridge [r₀] view to full repl view
7. Show right tape matches: replAsc(w-2) ++ [r_{w-1}] ++ origRight = repl.tail ++ origRight

The main difficulty is tracking list expressions through 4 phases and proving the connecting equalities (especially step 7, which requires `replAsc repl (w-1) = repl.tail`).

### Key insights from this session
- **Code bound**: `code < nPow n w` does NOT propagate through `code * n + c`. Must use `code < nPow n pos` (tight) and derive via `nPow_mono`.
- **replPrefix ordering**: the write loop pushes values in reverse order (r_k first, r_1 last). Must use ascending `replAsc` (snoc-based), not descending `replPrefix` (cons-based).
- **toBiTM pattern**: `unfold exactSteps` inlines `toBiTM`, breaking pattern matching for `shiftPhase_correct`. Use `exactSteps_succ` instead to keep `toBiTM` intact.
- **startShiftPhase if-chains**: must case-split on direction BEFORE proving the step, so each branch gives `step ... = some {concrete}` that `exactSteps_succ` can use.

## Key decisions

- **Tape-length precondition**: `left.length ≥ maxShift ∧ right.length ≥ maxShift` to avoid 0-padding mismatch between GS shiftBy and TM shift phase (both pad with 0 but produce structurally different lists)
- **New hypotheses**: `hAlpha` (alphabetSize≥1), `hBound` (replacement values < alphabetSize), `hCellBound` (cell values < alphabetSize)
- **TMPhase architecture reused**: same natToPhase/phaseToNat pattern for read/write as for shift

## History

| Date | Actor | Action |
|---|---|---|
| 2026-04-06 | LLM | Created plan based on architecture analysis |
| 2026-04-06 | LLM | Proved arithmetic helpers, natToPhase roundtrips for read/write, buildTransition lemmas. General theorem wired with 1 sorry in fullSim_general. |
| 2026-04-07 | LLM | Added all phase building blocks: exactSteps_append, readScan, biTM_step_lastRead, writeLoop, writeZeroShift. All fully proved (0 sorry in building blocks). fullSim_general composition: 1 sorry (chaining the phases). |
