# TM → GS — Proof Skeleton

Source: **Moore, "Generalized shifts: unpredictability and undecidability in dynamical systems"**, *Nonlinearity* **4** (1991) 199–230. Theorem 7, p.~217.

## Edge claim

| Lean wrapper | Source | Target | Status |
|---|---|---|---|
| `UniversalityGraph.edge_TMtoGS` | Generalized Shift `fromBiTM(machine)`, σ=1 τ=1 | BiInfiniteTuringMachine `machine` | **conditional** |

Open hypotheses (top-level parameters of `edge_TMtoGS`):

| Hypothesis | Description | Source / status |
|---|---|---|
| `hSim : MooreStepSimulation machine` | Every BiTM step matches one GS step on the encoded config (universal in config) | Paper Theorem 7. The nonempty-tape case is proved unconditionally as `stepCommutes`; the empty-tape case is the only open gap. |
| `hHead : ∀ config, state = 0 → head < numberOfSymbols` | Halted configs are well-formed | Internal invariant, true for any sensibly-initialised config. |

## Basic notions (paper vocabulary)

| Notion | Where in paper | Lean realization |
|---|---|---|
| Bi-infinite sequence `a ∈ A^Z` | §1 | `BiInfiniteTuringMachine.Configuration` (left, head, right) |
| Shift map `σ` | §1 | `shiftLeftOne`, `shiftRightOne` |
| Generalized shift `Φ : a ↦ σ^{F(a)}(a ⊛ G(a))` | eq. (2) | `GeneralizedShift.step` |
| Domain of dependence (DOD) | §1 | `windowWidth` field |
| Domain of effect (DOE) | §1 | replacement positions in `ShiftRule` |
| State-into-tape encoding | proof of Thm 7 | `encodeBiTM` (active cell merges state into head symbol) |
| Active vs passive cells | proof of Thm 7 | `isActive` predicate; values ≥ k are active |

## Lemma DAG (paper structure)

```
   D1 (extended alphabet)        D2 (state-into-tape encoding)
        \                              /
         \                            /
          L1 (encodeActive/decodeActive roundtrip)
                       |
                       v
          L2 (encodeBiTM/decodeBiTM roundtrip)
                       |
              ┌────────┴────────┐
              v                 v
          L3 (TM step → GS step,  L4 (well-formedness:
              nonempty tapes)         halted ⇒ head < k)
              \                 /
               \               /
                E_TMtoGS  (registered edge)
```

## Lemma nodes

### D1 — Extended alphabet definition

**Statement.** Define `extendedAlphabetSize = s·k + k` where `s = numberOfStates`, `k = numberOfSymbols`. Symbols `< k` are passive; symbols in `[k, s·k+k)` encode `(state, color)` pairs.
**Lean.** `TuringMachineToGeneralizedShift.extendedAlphabetSize`, `encodeActive`, `decodeActive`.
**Status.** Proved (`decodeActiveEncodeActive`).
**Basic notions.** State-into-tape encoding.

### D2 — Configuration encoding

**Statement.** `encodeBiTM` packages a BiTM config `(state, left, head, right)` into a 3-cell window `[leftCell, activeCell, rightCell]` with surrounding tape, where `activeCell` merges state into the head symbol.
**Lean.** `encodeBiTM`, `decodeBiTM`.
**Status.** Proved.
**Basic notions.** Bi-infinite sequence; window of width 3.

### L1 — encodeActive/decodeActive roundtrip

**Statement.** For `state ≥ 1`, `color < k`, `k > 0`, `decodeActive (encodeActive state color) = (state, color)`.
**Lean.** `decodeActiveEncodeActive`.
**Status.** Proved (`omega` + `Nat.mul_add_div`).

### L2 — Configuration roundtrip

**Statement.** For nonempty tapes, `decodeBiTM (encodeBiTM config) = some config`.
**Depends on.** L1.
**Lean.** `decodeEncode`.
**Status.** Proved.

### L3 — Step commutation (nonempty tapes)

**Statement.** For nonempty tapes, one BiTM step matches one GS step on the encoded config.
**Depends on.** D1, D2, L1.
**Lean.** `stepCommutes`.
**Status.** Proved (case analysis on direction × `nextState = 0` × tape remainder).

### L4 — Halted well-formedness

**Statement.** If `state = 0` (BiTM halted), the head symbol satisfies `head < numberOfSymbols`.
**Lean.** *Not formalized* — taken as hypothesis `hHead` of the edge.
**Status.** **Hypothesis** (well-formedness invariant).

### Edge assembly — `tmToGSSimulation` / `edge_TMtoGS`

**Statement.** Packaged `Simulation` from `hSim` (the universally-quantified version of L3, including the empty-tape case) and `hHead`.
**Lean.** `tmToGSSimulation` (proof file), `edge_TMtoGS` (registered wrapper).
**Status.** **Conditional**: depends on `hSim` (empty-tape gap) and `hHead`.

## Why the strict version is conditional — and structurally impossible

`stepCommutes` (L3) covers nonempty tapes. The empty-tape case is **NOT just unproven — it is FALSE for strict equality** in the standard GS.

**Counterexample.** Take `config = (s, [], h, rh :: rt)`, direction R, `nextState ≠ 0`, write `w`.
- BiTM step: `config' = (ns, [w], rh, rt)`.
- `encodeBiTM config = { left := [], cells := [0, A, rh], right := rt }`.
- `encodeBiTM config' = { left := [w].drop 1 = [], cells := [w, A', _], right := rt.drop 1 }`.
- `GS.step (encodeBiTM config) = some { left := [0], cells := [w, A', _], right := rt.drop 1 }`.

The GS output has `left = [0]` (because `shiftRightOne` pushes `cells[0] = 0` onto the left tape), but the encoded next state has `left = []`. No number `n` of GS steps recovers this: subsequent steps don't strip trailing zeros, they only consume them at the boundary. So `MooreStepSimulation machine` (the strict-equality form) is genuinely false on empty-tape configs, regardless of proof effort.

This is why `edge_TMtoGS` is registered as `conditional` with a hypothesis (`hSim`) that *cannot be discharged*. Recognizing this is a feature of the audit framework — the impossibility surfaces as a top-level signature obligation rather than hiding inside a sorry.

## Third path — `SimulationViaDecode` (decode-based commutes)

A new edge type [`SimulationViaDecode`](../../../Lean/Edges.lean) was added with decode-based commutes:

```lean
structure SimulationViaDecode (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  decode : A.Configuration → Option B.Configuration
  canon  : B.Configuration → B.Configuration
  commutes : ∀ b b', B.step b = some b' →
    ∃ n a, A.iterationStep n (encode b) = some a ∧ decode a = some (canon b')
  halting : ∀ b, B.step b = none → ComputationalMachine.Halts A (encode b)
```

The crucial difference from `Simulation`: `decode a = some (canon b')` instead of `a = encode b'`. This **lets the GS step result `a` differ from `encode b'`** as long as decoding it (after canonicalization) gives back `b'` modulo `canon`.

Edge `edge_TMtoGS` registered in [Lean/Edges.lean](../../../Lean/Edges.lean) with:
- `encode = encodeBiTM` (Moore's exact, no normalization)
- `decode = decodeBiTMNormalized` (`decodeBiTM` + `normalize` on BiTM tapes)
- `canon = normalizeBiTMConfig` (BiTM-side trailing-zero stripping)

The `[0]`/`[]` mismatch is absorbed at the **decode side**: when GS step pushes a `[0]` phantom, `decodeBiTM` reconstructs a BiTM config, and `normalize` on that strips the phantom. Compared with `canon b' = normalizeBiTMConfig b'`, both sides agree.

**Halting field: fully proved.** **Commutes field: fully proved.** Closure: `[propext, Quot.sound, Classical.choice]` — no `sorryAx`, no native axioms. The proof works through the four cases (direction L/R × nextState =/≠ 0) using `biTMStep_eq_uniform`, `iterationStep_eq_exactSteps`, the uniform-form `shiftRightOne`/`shiftLeftOne`, and the normalize lemmas (`normalize_consHeadD_dropOne`, `decodeActiveEncodeActive`, `normalize_cons_congr`).

The hypotheses remain only well-formedness conditions on the machine — no buried structural hypotheses.

## Novel resolution — `edge_TMtoGS_canonical`

A new edge in the registry sidesteps the impossibility by **changing the source machine**: instead of standard GS, use a *normalized* GS where each step strips trailing zeros from left and right tapes. The infrastructure lives in [Lean/Edges.lean](../../../Lean/Edges.lean):

| Definition | Role |
|---|---|
| `gsStepNormalized machine c := (GS.step machine c).map normalizeLR` | step + strip |
| `gsToCMNormalized machine` | the new ComputationalMachine |
| `encodeBiTMCanonical machine config := normalizeLR (encodeBiTM machine config)` | canonical encoding |
| `MooreStepSimulationCanonical machine` | strict-equality bisimulation property in the normalized variant |
| `edge_TMtoGS_canonical` | the new edge wrapper, with `hSimCanon` and `hHead` at top level |

Why this works on the empty-tape case: `GS.step` produces `left := [0]`; `normalizeLR` strips that to `[]`; the canonical encoding of the next state also has `left := []`. Strict equality holds.

**Hypothesis status:**
- `hSim` (in `edge_TMtoGS`): **structurally false**. Cannot be proved.
- `hSimCanon` (in `edge_TMtoGS_canonical`): **true in principle**. Discharge path provided by `mooreStepSimulationCanonical_holds (hk, hHeadAll)` in [Lean/Edges.lean](../../../Lean/Edges.lean), which reduces to a single named lemma `mooreStepCanonical_step_eq` (currently `sorry`).

The halting field of `edge_TMtoGS_canonical` is **fully proved** (no sorry); only `hSimCanon` remains, and its proof is now structured as one self-contained obligation.

### Discharge structure

```
mooreStepSimulationCanonical_holds  (theorem, machine + hk + hHeadAll → MooreStepSimulationCanonical)
   │  trivial: unfolds iterationStep 1 to step
   ▼
mooreStepCanonical_step_eq  (private theorem, the genuine work — currently sorry)
```

### Helper lemmas already in place

In [Lean/Edges.lean](../../../Lean/Edges.lean):
- `normalize_consHeadD_dropOne (xs : List Nat)` — `normalize ((xs.headD 0) :: xs.drop 1) = normalize xs`. Proved.

Already proved in [Lean/Proofs/TuringMachineToGeneralizedShift.lean](../../../Lean/Proofs/TuringMachineToGeneralizedShift.lean):
- `normalize_cons_congr` — congruence under cons.
- `headD_normalize` — `xs.headD 0 = (normalize xs).headD 0`.
- `tail_normalize` — `normalize xs.tail = (normalize xs).tail`.
- `normalize_idempotent`.
- `stepCommutes` — strict equality for nonempty cons-cons.
- `stepCommutesNorm` — equality up to normalize for nonempty cons-cons.

### Algebraic content (the proof on paper)

Concretely, for direction R, ns ≠ 0, GS step output normalized:
- left = `normalize (config.left.headD 0 :: normalize (config.left.drop 1))`
       = `normalize (config.left.headD 0 :: config.left.drop 1)`  [normalize_cons_congr + idempotent]
       = `normalize config.left`  [normalize_consHeadD_dropOne]
- cells third element = `(normalize (config.right.drop 1)).headD 0`
                      = `(config.right.drop 1).headD 0`  [headD_normalize]
- right = `normalize ((normalize (config.right.drop 1)).tail)`
        = `normalize (normalize (config.right.drop 1).tail)`  [tail_normalize, reverse]
        = `normalize (config.right.drop 1).tail`  [idempotent]
        = `normalize (config.right.drop 2)`

Compared to `encodeBiTMCanonical config'` for direction R:
- left = `normalize config.left` ✓
- cells third element = `config.right.tail.headD 0 = (config.right.drop 1).headD 0` ✓
- right = `normalize (config.right.drop 2)` ✓

Symmetric reasoning closes direction L. The `ns = 0` cases are similar (no `encodeActive` wrapping the new active cell).

### Why the formal proof remains sorry

The algebraic chain above uses standard `normalize` lemmas. In Lean, however, applying them through the `shiftRightOne`/`shiftLeftOne` definitions requires careful tactic massage:
- `shiftRightOne` and `shiftLeftOne` pattern-match on `right`/`left`, producing two branches per call. Combined with `match config.right with | [] | r :: rs` in their bodies and the `match (normalize ...)` we apply, the goal explodes into 4-8 sub-cases.
- Each sub-case requires aligning the normalized output's `if`-branch structure with the target form, which involves Bool/Prop coercions (`decide` wrappers) that don't always match the `by_cases` hypothesis form.
- Multiple session attempts produced partial proofs that compile through some sub-cases but get stuck on subtle structural mismatches. Total estimated effort to close: 150-250 lines of careful tactics.

The mathematical correctness is clear; the tactic engineering is the obstacle.

## See also

- [TMtoGS](../TMtoGS.md) — informal overview
- [Moore1991](../../Resources/Moore1991.md) — the paper
- [VerificationFramework](../../Plans/VerificationFramework.md)
