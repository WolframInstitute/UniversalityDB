# GS → TM — Proof Skeleton

Source: **Moore, "Generalized shifts: unpredictability and undecidability in dynamical systems"**, *Nonlinearity* **4** (1991) 199–230. Theorem 8, p.~218.

## Edge claim

| Lean wrapper | Source | Target | Status |
|---|---|---|---|
| `UniversalityGraph.edge_GStoTM` | BiInfiniteTuringMachine `toBiTM(params)`, σ=1 τ ≤ 2(w-1)+m | Generalized Shift `gsMachine(params)` | **conditional** |

Open hypotheses (top-level parameters of `edge_GStoTM`):

| Hypothesis | Description | Status |
|---|---|---|
| `hSim : StepSimulation params` | One GS step encoded as ≤ `2(w-1)+m` BiTM steps, for every config of correct width | Proved for `w=1` (`stepSimulation_w1`); `w≥2` open in `fullSim_general` |
| `hLen : reachable configs have correct window width` | Invariant of the GS family | Internal invariant |
| `hShift : every active window has shiftMagnitude ≥ 1` | Avoids degenerate non-shifting steps | Internal restriction |
| `hHalt : inactive GS configs encode to halting TM configs` | Halting correspondence | Internal correspondence |

## Basic notions

| Notion | Paper § | Lean realization |
|---|---|---|
| Window width `w` | §1 | `windowWidth : Nat` |
| Maximum shift `m` | §3 | `maxShift : Nat` |
| 3-phase TM construction (read, write, shift) | proof of Thm 8 | `TMPhase` inductive: `start | read | write | shift | halt` |
| Read phase | Thm 8 step 1 | `phaseTransition` for `TMPhase.read pos partialCode` |
| Write phase | Thm 8 step 2 | `phaseTransition` for `TMPhase.write pos windowCode` |
| Shift phase | Thm 8 step 3 | `phaseTransition` for `TMPhase.shift remaining goLeft` |
| Window-code encoding | implicit in proof | `encodeWindow`, `decodeWindow` |

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
   L2_read (read phase commutes)   L2_write (write phase commutes)
       |                            |
       └────────────┬───────────────┘
                    v
   L3 (stepSimulation_w1)        ←  proved in full
                    |
                    v
   L4 (fullSim_general, w≥2)     ←  has `sorry` (composition of 4 phases via exactSteps_append)
                    |
                    v
   E_GStoTM  (registered edge)    ←  uses gsToTMCommutes; depends on hSim
```

## Lemma nodes

### D1 — `TMPhase` inductive

**Statement.** TM internal state modeled as `halt | start | read pos partialCode | write pos windowCode | shift remaining goLeft`.
**Lean.** `TMPhase`.
**Status.** Defined.
**Basic notions.** 3-phase construction.

### D2 — Phase ↔ Nat encoding

**Statement.** Bijection `phaseToNat`/`natToPhase` for compatibility with `TuringMachine.Machine`'s Nat-state convention.
**Lean.** `phaseToNat`, `natToPhase`.
**Status.** Proved.

### D3 — `phaseTransition`

**Statement.** Pattern-matched transition function on `TMPhase`. Each phase reads/writes one cell and transitions to the next phase.
**Lean.** `phaseTransition`, `buildTransition`.
**Status.** Defined.

### L1 — Window code roundtrip

**Statement.** `decodeWindow alphabetSize w (encodeWindow alphabetSize window) = window` for `window.length = w` and `∀ x ∈ window, x < alphabetSize`.
**Lean.** `decodeWindow_encodeWindow`.
**Status.** Proved.
**Basic notions.** Window-code encoding.

### L2_read — Read phase commutes

**Statement.** Starting from `start` phase, after `w-1` BiTM steps the TM is in `read (w-1) (encodeWindow window)` with head positioned just past the window.
**Lean.** `readScan`, `lastRead`.
**Status.** Proved.
**Basic notions.** Read phase.

### L2_write — Write phase commutes

**Statement.** From `write 0 windowCode` phase, after `w-2` BiTM steps the replacement word is written back right-to-left and the TM is in `writeZeroShift`.
**Lean.** `writeLoop`, `writeZeroShift`.
**Status.** Proved.
**Basic notions.** Write phase.

### L3 — `stepSimulation_w1`

**Statement.** For window width 1, one GS step = bounded TM steps.
**Lean.** `stepSimulation_w1`.
**Status.** Proved.

### L4 — `fullSim_general` (w ≥ 2)

**Statement.** For w ≥ 2, the four-phase composition (read, write, shift) closes. Goal: chain `readScan + lastRead + writeLoop + writeZeroShift + shift_bridge` via `exactSteps_append`.
**Lean.** `fullSim_general`, line 1276.
**Status.** **`sorry`** — composition argument not closed; the building blocks exist.
**Basic notions.** All three phases composed.

### Edge assembly — `gsToTMCommutes` / `edge_GStoTM`

**Lean.** `gsToTMCommutes` (proof file, uses `hSim` parameter), `edge_GStoTM` (registered wrapper).
**Status.** **Conditional** on the four hypotheses. The wrapper avoids the buried `sorry` in the original `gsToTMSimulation` by hoisting.

## See also

- [GStoTM](../GStoTM.md) — informal overview
- [GStoTM_GeneralWidth](../../Plans/GStoTM_GeneralWidth.md) — plan for closing the w≥2 gap
- [Moore1991](../../Resources/Moore1991.md) — the paper
