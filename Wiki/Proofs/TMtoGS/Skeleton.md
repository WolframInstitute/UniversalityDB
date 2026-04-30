# TM → GS — Proof Skeleton

Source: **Moore, "Generalized shifts: unpredictability and undecidability in dynamical systems"**, *Nonlinearity* **4** (1991) 199–230. Theorem 7, p. 217.

## Edge claim

| Lean wrapper | Source | Target | Status |
|---|---|---|---|
| `UniversalityGraph.edge_TMtoGS` | Generalized Shift `fromBiTM(machine)`, σ=1 τ=1 | `BiInfiniteTuringMachine.toComputationalMachineNormalized machine` | **conditional** (well-formedness only) |

Hypotheses (top-level parameters):

| Hypothesis | Description |
|---|---|
| `hk : numberOfSymbols > 0` | nontrivial alphabet |
| `hHeadAll : ∀ c, c.head < numberOfSymbols` | every config has a valid head symbol |
| `hWriteBound : ∀ q a, transition.write < numberOfSymbols` | transitions write inside the alphabet |
| `hStateBound : ∀ q a, transition.nextState ≤ numberOfStates` | transitions land in valid states |

All four are well-formedness conditions on the machine itself — no buried structural hypotheses.

## Structure form

Returns `ComputationalMachine.SimulationEncoding` (the conjugation form). The fields are `encode`, `decode`, `commutes`, `halting`. `commutes` reads as the strict conjugation
```
step_B(b) = decode (step_A^n (encode b))
```
The B side is `BiInfiniteTuringMachine.toComputationalMachineNormalized machine` — Moore's step post-composed with `stripConfig` (strip trailing zeros from both tapes). Because B's step always lands in canonical form, the conjugation is strict (no `modulo normalize` qualifier). The bridge to Moore's exact step is `BiInfiniteTuringMachine.step_stripConfig_bisim`, a separate lemma.

## Basic notions (paper vocabulary)

| Notion | Where in paper | Lean realization |
|---|---|---|
| Bi-infinite sequence `a ∈ A^Z` | §1 | `BiInfiniteTuringMachine.Configuration` (left, head, right) |
| Shift map `σ` | §1 | `shiftLeftOne`, `shiftRightOne` |
| Generalized shift `Φ : a ↦ σ^{F(a)}(a ⊛ G(a))` | eq. (2) | `GeneralizedShift.step` |
| Domain of dependence (DOD) | §1 | `windowWidth` field |
| State-into-tape encoding | proof of Thm 7 | `encodeBiTM` (active cell merges state into head symbol) |
| Active vs passive cells | proof of Thm 7 | values ≥ k are active |

## Lemma DAG

```
   D1 (extended alphabet)        D2 (state-into-tape encoding)
        \                              /
         \                            /
          L1 (encodeActive/decodeActive roundtrip)
                       |
                       v
          L2 (encodeBiTM/decodeBiTM roundtrip)
                       |
                       v
          L3 (stepCommutes — Moore-step on nonempty tapes)
                       |
                       v
          L4 (tmToGSCommutesMoore — Moore-step, all tapes,
              decodes-to-normalized)
                       |
                       v
          L5 (decodeBiTMNormalized_encode_eq +
              normalizeBiTMConfig_eq_stripConfig)
                       |
                       v
          tmToGSSimulation  →  edge_TMtoGS
```

## Lemma nodes

### D1 — Extended alphabet

`extendedAlphabetSize = s·k + k`. Symbols `< k` passive; symbols in `[k, s·k+k)` encode `(state, color)` pairs.
**Lean.** `TuringMachineToGeneralizedShift.encodeActive`, `decodeActive`, `extendedAlphabetSize`.

### D2 — Configuration encoding

`encodeBiTM` packages `(state, left, head, right)` into a 3-cell window, with `activeCell` merging state into head.
**Lean.** `encodeBiTM`, `decodeBiTM`.

### L1 — Alphabet roundtrip

For `state ≥ 1`, `color < k`, `k > 0`: `decodeActive (encodeActive state color) = (state, color)`.
**Lean.** `decodeActiveEncodeActive`. Proved.

### L2 — Configuration roundtrip

For nonempty tapes: `decodeBiTM (encodeBiTM config) = some config`.
**Lean.** `decodeEncode`. Proved.

### L3 — Step commutation (nonempty tapes, strict)

For nonempty tapes, one BiTM step matches one GS step on the encoded config.
**Lean.** `stepCommutes`. Proved.

### L4 — Step commutation against Moore's exact step

Given `step machine b = some moore_b'`, produces an n-step GS witness `a` with `decode a = some (normalizeBiTMConfig moore_b')`. Handles direction L/R × nextState =/≠ 0 × empty/nonempty tapes uniformly.
**Lean.** `TMtoGS.tmToGSCommutesMoore`. Proved (no `sorry`).

### L5 — Bridge to canonical form

- `decodeBiTMNormalized_encode_eq` — encoding then decoding-with-normalization recovers the canonical form.
- `normalizeBiTMConfig_eq_stripConfig` — `normalizeBiTMConfig = BiInfiniteTuringMachine.stripConfig` (one-line proof; the two functions are literally identical bodies in different namespaces).

These let the conjugation field land at `b'` directly when B's step is `stepNormalized` (which post-strips).

### Edge assembly — `tmToGSSimulation` / `edge_TMtoGS`

A thin wrapper over `tmToGSCommutesMoore`: extract `moore_b'` from `stepNormalized = some b'`, run L4, bridge via L5.

**Status.** Closed. Closure: `[propext, Quot.sound, Classical.choice]` — no `sorryAx`, no native axioms.

## The `[0]` phantom — and how it's absorbed

For empty-tape configs, GS step produces `left = [0]` (because `shiftRightOne` pushes `cells[0] = 0` onto the left tape), but Moore's exact-step result has `left = []`. Strict equality fails.

This is structurally why `MooreStepSimulation` (the old strict-equality form) was false in general. Two paths absorb it:

1. **Decode-side absorption (current).** L4 lands at `normalizeBiTMConfig moore_b'`, which strips the phantom on the BiTM side. Moore's exact step is preserved; only the decode normalizes.
2. **Step-side absorption.** Use `BiInfiniteTuringMachine.stepNormalized` (Moore + post-strip) as the B-side step. Then `b'` is canonical and L4's conclusion lines up with `b'` directly.

The current edge uses both — it targets the normalized B-side step and uses the decode-with-normalization as decode, so the conjugation reads strictly.

## See also

- [TMtoGS](../TMtoGS.md) — informal overview
- [Moore1991](../../Resources/Moore1991.md) — the paper
- [VerificationFramework](../../Plans/VerificationFramework.md)
