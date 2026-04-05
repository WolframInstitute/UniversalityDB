# Plan: Current Focus

> Status: **draft**

## Goal

Close the remaining sorry in GS → TM (Moore Theorem 8) step simulation, completing the bidirectional TM ↔ GS equivalence.

## Steps

- [x] Define GS machine family in Lean
- [x] Define TM → GS encoding (Theorem 7) — fully proved
- [x] Define GS → TM encoding (Theorem 8) — roundtrips proved
- [x] Prove window encoding roundtrip (`decodeWindow_encodeWindow`)
- [x] Prove config encoding roundtrip (`decodeConfig_encodeConfig`)
- [ ] Prove `stepSimulation_w1` active case — the last sorry
- [ ] Generalize from windowWidth=1 to arbitrary widths

## Decisions

- GS always moves: `shiftMagnitude >= 1` precondition on active windows.
- Tape normalization: `normalize` strips trailing zeros; roundtrip lemmas work up to normalization.
- Window roundtrip proved via snoc induction (no `List.reverseRecOn` in Lean 4 core).

## Approach for the last sorry

Three phase lemmas needed (see `working.md` for full analysis):
1. Shift phase lemma (induction on remaining count)
2. Write phase lemma (induction on position)
3. Read phase lemma (induction on position)
4. Combine: read (w-1) + write (w-1) + shift (m) = 2(w-1)+m steps

## History

| Date | Actor | Action |
|---|---|---|
| 2026-04-05 | LLM | Created plan from working.md and proof status |
