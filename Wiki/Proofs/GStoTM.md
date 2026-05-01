# GS → Turing Machine (Moore Theorem 8)

Any generalized shift is conjugate to a bi-infinite Turing machine, with overhead σ=1, τ ≤ 2(w−1)+m where w is the window width and m is the shift magnitude of the active rule.

## Encoding

A GS configuration `{left, cells, right}` (with `cells.length = w`) encodes as a TM configuration `{state := 1, left, head := cells[0], right := cells.tail ++ right}` — the head sits on the leftmost window cell and the rest of the window is prepended to the right tape.

Each GS step is simulated by `2(w−1) + m` TM steps in three phases. The TM uses a Nat-state encoding through the inductive `TMPhase` type:

| Phase | TM steps | Effect |
|---|---|---|
| **Read** (`TMPhase.read pos partialCode`) | `w − 1` | scan right, accumulate window contents in state |
| **Write** (`TMPhase.write pos windowCode`) | `w − 1` (last step of read + w−2 write loop) | write replacement symbols right-to-left |
| **Shift** (`TMPhase.shift remaining goLeft`) | `m` | move head to match GS shift |

## Decode

`decodeConfigPadded w` recovers a multi-cell GS view from a TM config: it reads `w − 1` cells from the right tape after the head, padding with `0` if the right tape underflows. The padding absorbs the `[0]`-phantom that arises when a short-tape `shiftRightOne` writes a default 0. This is symmetric to TM → GS, where `stripConfig` on the BiTM side absorbs the analogous trailing-zero phantom.

## Lean formalization

[Lean/Proofs/GeneralizedShiftToTuringMachine.lean](../../Lean/Proofs/GeneralizedShiftToTuringMachine.lean)

Key building blocks:

- `GSParams`, `gsMachine`, `toBiTM` — parameter record + machine constructions.
- `TMPhase` (inductive: `halt | start | read | write | shift`), `phaseToNat` / `natToPhase` — proof-friendly state representation.
- `phaseTransition`, `buildTransition` — pattern-matched transition.
- `encodeConfig` / `decodeConfig` / `decodeConfigPadded` — bridge between GS and TM configs.
- `replAsc`, `replAsc_eq_tail` — `[repl[1], …, repl[w−1]] = repl.tail` when `repl.length = w`.

Phase lemmas:

- `readScan`, `biTM_step_lastRead` — `w − 1` steps + the last read step that transitions into the write phase.
- `writeLoop` — `w − 2` write steps in uniform `k`-step form (no w=2 vs w≥3 split).
- `writeZeroShift` — `m` steps of the shift phase.

Composed chain (w ≥ 2):

- **`fullSim_general_cView`** — discharges `2(w−1) + m` TM steps from `encodeConfig {left, cells, right}` to `encodeConfig (shiftBy {left, [repl[0]], replAsc repl (w−1) ++ right} m dir)`, the [c]-view of the multi-cell shift target. **Empty axiom closure.**

For w = 1: `fullSim_w1` handles the simpler case (start phase + shift phase, no read/write).

Bridge (decode commutes with shift in the [c]-view):

- `decodePadded_shiftRightOne` — unconditional per-step bridge.
- `decodePadded_shiftLeftOne` — per-step bridge with precondition `right.length ≥ w−1`. The precondition is *necessary* because multi-cell shiftLeft pushes the rightmost cell (a padding 0 when the right tape is short) onto the right tape, while [c]-view shiftLeft pushes the original `c`. The precondition is preserved by shiftLeft (which only grows the right tape), so it propagates through the `shiftBy mag true` induction.
- `decodePadded_shiftByRight` / `decodePadded_shiftByLeft` — full bridges by induction on `mag`, chained via `Option.map_map`.

Edge proof:

- `gsToTMSimulationEncoding` — branches on w=1 vs w≥2; combines `fullSim_*` with the appropriate full bridge.

The wrapper `edge_GStoTM` lives in [Lean/Edges.lean](../../Lean/Edges.lean).

**Status.** 0 sorry. Axiom closure: `[propext, Quot.sound, Classical.choice]`. Conditional only on seven well-formedness hypotheses on the GS family (`hAlpha`, `hWidth`, `hLen`, `hShift`, `hRepl`, `hCellBoundAll`, `hHalt`).

## See also

- [TMtoGS](TMtoGS.md) — the forward direction (Moore Theorem 7)
- [TuringMachine](../Systems/TuringMachine.md), [GeneralizedShift](../Systems/GeneralizedShift.md) — the systems
- [SimulationEncoding](../Concepts/SimulationEncoding.md) — the structure form used here
- [Moore1991](../Resources/Moore1991.md) — the paper
- [Skeleton](GStoTM/Skeleton.md) — paper-driven layered DAG
