# GS → TM — Proof Skeleton

Source: **Moore, "Generalized shifts: unpredictability and undecidability in dynamical systems"**, *Nonlinearity* **4** (1991) 199–230. Theorem 8, p. 218.

## Edge claim

| Lean wrapper | Source | Target | Status |
|---|---|---|---|
| `UniversalityGraph.edge_GStoTM` | BiInfiniteTuringMachine `toBiTM(params)`, σ=1 τ ≤ 2(w−1)+m | Generalized Shift `gsMachine(params)` | **conditional** (7 well-formedness hypotheses); 0 sorry |

Top-level parameters of `edge_GStoTM`:

| Hypothesis | Description |
|---|---|
| `hAlpha : alphabetSize ≥ 1` | Non-empty alphabet |
| `hWidth : windowWidth ≥ 1` | Non-empty window |
| `hLen` | Reachable GS configs have cells of length `windowWidth` |
| `hShift` | Active windows have shiftMagnitude ≥ 1 |
| `hRepl` | Active windows have replacement length = `windowWidth` |
| `hCellBoundAll` | Reachable GS configs have alphabet-bounded cells |
| `hHalt` | Inactive GS configs encode to halting TM configs |

## Basic notions

| Notion | Paper § | Lean realization |
|---|---|---|
| Window width `w` | §1 | `params.windowWidth` |
| Maximum shift `m` | §3 | `(params.gsTransition cells).shiftMagnitude` |
| 3-phase TM construction | proof of Thm 8 | `TMPhase`: `halt \| start \| read \| write \| shift` |
| Read phase | step 1 | `phaseTransition` for `TMPhase.read` |
| Write phase | step 2 | `phaseTransition` for `TMPhase.write` |
| Shift phase | step 3 | `phaseTransition` for `TMPhase.shift` |
| Window-code encoding | implicit | `encodeWindow`, `decodeWindow` |
| [c]-view ↔ multi-cell view | implicit | `decodeConfigPadded` (with 0-padding) |

## Lemma DAG

```
   D1 (TMPhase inductive)         D2 (Nat ↔ TMPhase encoding)
        \                              /
         \                            /
          D3 (phaseTransition)
                  |
                  v
          L1 (encodeWindow / decodeWindow roundtrip)
                  |
       ┌──────────┴─────────────────┐
       v                            v
   L2_read (read phase, w-1 steps)  L2_write (write phase, w-2 steps)
       |                            |
       └────────────┬───────────────┘
                    v
             L3_shift (shift phase, m steps; writeZeroShift)
                    |
                    v
   L4 (fullSim_general_cView, w≥2) ←  empty axiom closure
                    |                  ──── plus ────
                    v
              fullSim_w1 (w=1 special case)
                    |
                    v
   B1 (decodePadded_shiftRightOne) — per-step bridge, unconditional
   B2 (decodePadded_shiftLeftOne)  — per-step bridge, requires right.length ≥ w-1
                    |
                    v
   B3 (decodePadded_shiftByRight / decodePadded_shiftByLeft) — full bridges by induction on mag
                    |
                    v
   B4 (replAsc_eq_tail) — replAsc repl (w-1) = repl.tail when repl.length = w
                    |
                    v
   gsToTMSimulationEncoding (commutes + halting)
                    |
                    v
   E_GStoTM (registered edge)        ←  [propext, Quot.sound, Classical.choice]
```

## Lemma nodes

### D1 — `TMPhase` inductive

**Statement.** TM internal state modeled as `halt | start | read pos partialCode | write pos windowCode | shift remaining goLeft`.
**Lean.** `TMPhase`.
**Status.** Defined.

### D2 — Phase ↔ Nat encoding

**Statement.** Bijection `phaseToNat` / `natToPhase` for compatibility with `TuringMachine.Machine`'s Nat-state convention.
**Lean.** `phaseToNat`, `natToPhase`, `natToPhase_*` lemmas.
**Status.** Proved.

### D3 — `phaseTransition`

**Statement.** Pattern-matched transition function on `TMPhase`. Each phase reads/writes one cell and transitions to the next phase.
**Lean.** `phaseTransition`, `buildTransition`.
**Status.** Defined.

### L1 — Window code roundtrip

**Statement.** `decodeWindow alphabetSize w (encodeWindow alphabetSize window) = window` for `window.length = w` and `∀ x ∈ window, x < alphabetSize`.
**Lean.** `decodeWindow_encodeWindow`.
**Status.** Proved.

### L2_read — Read phase

**Statement.** From `start` phase, after `w−1` BiTM steps the TM is in `read (w−1) (encodeWindow window)` with head positioned at the last window cell. One more step (`biTM_step_lastRead`) transitions into the write phase.
**Lean.** `readScan`, `biTM_step_lastRead`.
**Status.** Proved.

### L2_write — Write phase

**Statement.** From `writeState (w−1) windowCode`, the next `w−2` BiTM steps write the replacement word right-to-left, leaving the TM in `writeState 0 windowCode`.
**Lean.** `writeLoop` (uniform k-step form).
**Status.** Proved.

### L3_shift — Shift phase

**Statement.** From `writeState 0 windowCode`, the next `m` BiTM steps execute the shift, landing back in `state := 1` with the shifted [c]-view.
**Lean.** `writeZeroShift`.
**Status.** Proved.

### L4 — `fullSim_general_cView` (w ≥ 2)

**Statement.** For w ≥ 2, the four-phase composition (read, last-read, write loop, write-zero-shift) closes. After `2(w−1) + m` BiTM steps, the TM reaches `encodeConfig (shiftBy {left, [repl[0]], replAsc repl (w−1) ++ right} m dir)`, the [c]-view of the multi-cell shift target.
**Lean.** `fullSim_general_cView`.
**Status.** Proved. **Empty axiom closure.**

### `fullSim_w1` (w = 1 special case)

**Statement.** For w = 1, `m` BiTM steps suffice (no read/write phases — start phase reads the single cell and dispatches directly into the shift phase).
**Lean.** `fullSim_w1`.
**Status.** Proved.

### B1 — Per-step bridge for shiftRightOne

**Statement.** `decodeConfigPadded w (encodeConfig (shiftRightOne X)) = (decodeConfigPadded w (encodeConfig X)).map shiftRightOne` for any [c]-view config X. Unconditional.
**Lean.** `decodePadded_shiftRightOne`.
**Status.** Proved.
**Why it holds.** shiftRightOne does not push to the right tape, so the [c]-view's right and the multi-cell decode agree on the shifted form (modulo the cell padding that decodePadded reconstructs uniformly).

### B2 — Per-step bridge for shiftLeftOne

**Statement.** `decodeConfigPadded w (encodeConfig (shiftLeftOne X)) = (decodeConfigPadded w (encodeConfig X)).map shiftLeftOne` for any [c]-view config X with `right.length ≥ w − 1`.
**Lean.** `decodePadded_shiftLeftOne`.
**Status.** Proved with precondition.
**Why the precondition is necessary.** Multi-cell shiftLeft pushes the *rightmost cell of the window* onto the right tape. When `right.length < w − 1`, the multi-cell view has padding-0 cells in the window, and the rightmost is a 0; the [c]-view, by contrast, pushes the original `c` and grows by one cell — so the right tapes diverge. With `right.length ≥ w − 1`, no padding is needed and the rightmost window cell is a real cell that the [c]-view's right tape can supply on the next step.
**Why the precondition propagates.** shiftLeftOne sends `right ↦ c :: right`, which only *grows* the right tape; if the precondition holds at the start of `shiftBy mag true`, it holds throughout.

### B3 — Full bridges (induction on mag)

**Statement.** Same as B1/B2 but for arbitrary `shiftBy mag dir`.
**Lean.** `decodePadded_shiftByRight` (unconditional), `decodePadded_shiftByLeft` (with precondition).
**Status.** Proved by induction on `mag`, chaining via `Option.map_map`.

### B4 — `replAsc_eq_tail`

**Statement.** `replAsc repl (w − 1) = repl.tail` when `repl.length = w` and `w ≥ 1`. Identifies the chain output's right-tape prefix with `repl.tail`.
**Lean.** `replAsc_eq_tail` (via helper `replAsc_cons_eq_take`).
**Status.** Proved.

### Edge assembly — `gsToTMSimulationEncoding` / `edge_GStoTM`

**Statement.** Combines L4 (or `fullSim_w1`), B3, and B4: after `2(w−1) + m` BiTM steps from `encodeConfig b`, decoding via `decodeConfigPadded` yields `step_GS b`.
**Lean.** `gsToTMSimulationEncoding` (commutes + halting), `edge_GStoTM` (registered wrapper).
**Status.** Proved. Closure: `[propext, Quot.sound, Classical.choice]`.

## See also

- [GStoTM](../GStoTM.md) — informal overview
- [TMtoGS/Skeleton](../TMtoGS/Skeleton.md) — the symmetric direction
- [Moore1991](../../Resources/Moore1991.md) — the paper
