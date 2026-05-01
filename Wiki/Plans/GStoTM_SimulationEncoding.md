# Plan: GS → TM as `SimulationEncoding` (full proof, no sorry)

## Goal

Produce a `ComputationalMachine.SimulationEncoding` for GS → TM (Moore Theorem 8) with **0 sorry**, mirroring the `SimulationEncoding` form already used by TM → GS in [Lean/Proofs/TMtoGS.lean](../../Lean/Proofs/TMtoGS.lean).

The current state has 1 sorry in `fullSim_general` (the structural-equality / multi-cell-view form), which can't be discharged without a tape-length precondition. The `SimulationEncoding` (conjugation) form bypasses this by using a *padded decode*.

## Strategy: `[c]`-view chain + `decodeConfigPadded` bridge

The chain of 4 phases (`readScan` + `biTM_step_lastRead` + `writeLoop` + `writeZeroShift`) naturally lands at the **one-cell view** `encodeConfig (shiftBy {left, [r₀], replAsc(w-1) ++ right} mag dir)` — no tape-length precondition needed.

A padded decode `decodeConfigPadded w` (which pads cells with `0` to width `w` when the right tape is shorter than `w-1`) bridges this to the proper `w`-cell view of `shiftBy`. The `[0]` phantom from short-tape shifts is absorbed at decode time, just like trailing-zero canonicalization absorbs it on the BiTM side in TM → GS.

**No normalized machines needed** for this direction — the standard `step` suffices because the TM evolution doesn't introduce trailing zeros (it just consumes the tape with default-0 reads), and `decodeConfigPadded` re-flattens with proper padding.

## Steps

- [x] **Step 1 — Discharge `fullSim_general_cView` (the chain).** ✅ Fully proved on 2026-05-01.
  Add a new private theorem `fullSim_general_cView` with conclusion landing at the `[c]`-view (using `replAsc repl (windowWidth - 1) ++ right`). Discharge by chaining via `exactSteps_append`:
  - `readScan` (line ~1003): `w-1` steps
  - `biTM_step_lastRead` (line ~1079): 1 step
  - `writeLoop` (line ~1131): `w-2` steps (skip if `w=2`; case-split)
  - `writeZeroShift` (line ~1195): `mag` steps
  Total: `2(w-1) + mag`. Estimated 80–150 lines.

  **Tactic notes:** the right-tape rewrite `(c₁::rest)++right = init++(last::right)` requires careful handling — `rw [hsplit]` rewrites *all* occurrences of `c₁::rest` including ones nested inside `.dropLast`/`.getLast`. Use `conv => lhs => rw [hsplit]` (Lean 4 syntax — `conv_lhs` is not in this project's tactic set without Mathlib), or `nth_rewrite` if available, or pre-generalize with `generalize` before rewriting.

- [x] **Step 2 — Define `decodeConfigPadded`.** ✅ Defined; static bridge `decodeConfigPadded_encodeConfig` proved.
  ```lean
  def decodeConfigPadded (windowWidth : Nat) (tmConfig : BiInfiniteTuringMachine.Configuration)
      : Option GeneralizedShift.Configuration :=
    if tmConfig.state ≠ 1 then none
    else
      let prefix := tmConfig.right.take (windowWidth - 1)
      let pad := List.replicate (windowWidth - 1 - prefix.length) 0
      some { left := tmConfig.left,
             cells := tmConfig.head :: (prefix ++ pad),
             right := tmConfig.right.drop (windowWidth - 1) }
  ```

- [x] **Step 3 — Per-step bridge.** ✅ `decodePadded_shiftRightOne` (unconditional) and `decodePadded_shiftLeftOne` (with precondition `right.length ≥ w-1`) discharged on 2026-05-01. shiftLeft requires the precondition because multi-cell shiftLeft pushes the rightmost cell (possibly a padding 0) onto the right tape, while [c]-view shiftLeft pushes the original `c`. The precondition is preserved by shiftLeft (which only grows the right tape).

- [x] **Step 4 — Induction-on-`mag` to get full bridge.** ✅ `decodePadded_shiftByRight` (unconditional) and `decodePadded_shiftByLeft` (with precondition) proved by induction on mag, chaining via `Option.map_map`. Plus `replAsc_eq_tail` discharged via helper `replAsc_cons_eq_take`.

- [x] **Step 5 — Build `gsToTMSimulationEncoding`.** ✅ Discharged. Branches on w=1 (uses `fullSim_w1` + bridges) vs w≥2 (uses `fullSim_general_cView` + bridges + `replAsc_eq_tail`). Closure: `[propext, Quot.sound, Classical.choice]`.

- [x] **Step 6 — Update `Edges.lean` `edge_GStoTM`.** ✅ Returns `SimulationEncoding`; registry's `claimShape := .simulationEncoding`. Notes updated to reflect full discharge.

- [x] **Step 7 — Verify.** ✅ Build passes; integrity check reports `fullSim_general_cView: []` (clean) and `gsToTMSimulationEncoding: [propext, Quot.sound, Classical.choice]` (clean — no sorryAx). Sorry count: 2 (only pre-existing in TagSystemToCTS and CockeMinsky, unchanged).

## Why this fits the framework

**Symmetric to TM → GS** (already done):

| | TM → GS (done) | GS → TM (this plan) |
|---|---|---|
| Source machine A | `GeneralizedShift.toComputationalMachine` | `BiInfiniteTuringMachine.toComputationalMachine` |
| Target machine B | `BiInfiniteTuringMachine.toComputationalMachineNormalized` | `GeneralizedShift.toComputationalMachine` |
| Phantom absorbed by | Stripping on the BiTM (B) side via `stepNormalized` | Padding cells in `decodeConfigPadded` (decode side) |
| Structure | `SimulationEncoding` | `SimulationEncoding` |
| `decode` | `decodeBiTMNormalized` | `decodeConfigPadded` |

The **per-direction asymmetry**: TM → GS uses the normalized BiTM step because the `[0]` phantom appears on the BiTM tape. GS → TM uses the padded decode because the `[0]` phantom appears in the GS cells (when `shiftBy` underflows). Both achieve the conjugation form `step_B(b) = decode (step_A^n (encode b))` cleanly.

## Risks

The chain proof itself is a standard composition via `exactSteps_append`, but the **list bookkeeping** is intricate. Key sources of friction:

- The right-tape rewrite (already hit) — needs `conv => lhs` or pre-generalization to avoid recursive rewriting.
- The `init.reverse ++ c₀::origLeft` ↔ `l :: (ls ++ left₀)` reformulation for `writeLoop`'s input form — case split on `w=2` vs `w≥3`.
- `replAsc_succ_append` to convert `replAsc(w-2) ++ (repl[w-1] :: right)` to `replAsc(w-1) ++ right`.

**The CLAUDE.md "max 3 attempts" rule applies** — if any single proof obligation fails after 3 distinct approaches, stop and report.

## Decisions

- **No tape-length precondition.** The user explicitly preferred handling normalization via the simulation framework rather than adding hypotheses.
- **No normalized GS machine.** The deferred GS bisim lemma (`Lean/Machines/GeneralizedShift/Defs.lean` line ~194-203) is *not* needed for this direction — `decodeConfigPadded` does the work.
- **Keep `gsToTMCommutes`/`stepSimulation`/`StepSimulation` for backward compatibility** initially; can be deleted later if `gsToTMSimulationEncoding` makes them redundant.

## History

| Date | Actor | Action |
|---|---|---|
| 2026-05-01 | LLM | Created plan; identified `decodeConfigPadded` approach; began chain proof, hit tactic-engineering friction on right-tape rewrite, deferred to scheduled session. |
| 2026-05-01 | LLM | Resumed in dedicated session. Refactored `writeLoop` to uniform k-step form (eliminates w=2 vs w≥3 split). Added `chain_left_form` + `chain_getLastD` helpers. Discharged `fullSim_general_cView` fully (0 sorry, axiom closure `[]`). Defined `decodeConfigPadded` and proved static bridge. Stubbed per-step bridges and full bridge with `sorry`; struggled with Lean tactic engineering of the case analysis (multi-cell vs [c]-view shifts diverge by trailing-0 padding which `decodeConfigPadded` reconciles, but `Configuration` lacking `[ext]` made `congr 1; ext1` paths messy). Updated `edge_GStoTM` to `SimulationEncoding` shape; registry `claimShape := .simulationEncoding`. Build passes; `Integrity` check reports `fullSim_general_cView : []` (no propext, no choice, no sorry) and `gsToTMSimulationEncoding : [propext, sorryAx]` (sorryAx tracked from the deferred bridge). Stopping per max-3-attempts rule on bridge tactic engineering. |
| 2026-05-01 | LLM | Resumed; user asked to push and finish. Realized the per-step bridge for shiftLeft does NOT hold unconditionally — multi-cell shiftLeft pushes a padding-0 to the right tape when the right is short, while [c]-view shiftLeft pushes the original `c`. Added precondition `right.length ≥ w-1` (preserved by shiftLeft, which only grows right). Proved `decodePadded_shiftRightOne` (unconditional) using helper rfl-lemmas `shiftRightOne_singleton_{nil,cons}` + `shiftRightOne_cons_{nil,cons}` and key list lemmas `List.dropLast_concat`, `List.getLastD_concat`, `List.take_succ_eq_append_getElem`, `List.drop_eq_getElem_cons`. Added `decodePadded_proper_form` helper (decode without padding when right.length ≥ w-1). Proved `decodePadded_shiftLeftOne` cleanly using this. Proved full bridges `decodePadded_shiftByRight` / `decodePadded_shiftByLeft` by induction on mag, chaining via `Option.map_map`. Proved `replAsc_eq_tail` via helper `replAsc_cons_eq_take`. Discharged `gsToTMSimulationEncoding.commutes` with explicit witnesses (no `set`/`convert`/`by_contra` — these aren't in core Lean). Build passes with axiom closure `[propext, Quot.sound, Classical.choice]` (NO sorryAx). `EDGE AUDIT: PASS (10 edges)`. Sorry count unchanged at 2 (pre-existing, unrelated). |
