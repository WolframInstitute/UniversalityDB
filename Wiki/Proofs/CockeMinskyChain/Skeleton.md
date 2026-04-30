# Cocke-Minsky Chain — Proof Skeleton

The composed chain `any TM →[Cocke-Minsky 1964] 2-Tag →[Cook 2004] CTS →[Smith 2007] (2,3) TM`. Establishes that Wolfram's (2,3) Turing machine is Turing-universal.

## Edge claim

| Lean wrapper | Source | Target | Status |
|---|---|---|---|
| `UniversalityGraph.edge_CockeMinskyChain` | Wolfram's (2,3) TM | Every TM (`IsUniversal wolfram23`) | **conditional** |

Open hypotheses (top-level parameters):

| Hypothesis | Paper | Status |
|---|---|---|
| `h_cm : ∀ machine, CockeMinskyStepSimulation machine` | Cocke 1964 / Minsky 1967, Ch. 14 | Hypothesis (sketch only formalized; full multi-phase doubling/halving sweep is the gap) |
| `h_smith : SmithSimulation` | Smith 2007 | **Hypothesis only** (per project policy: not formalized — too complex; 6 intermediate systems) |

## Basic notions

| Notion | Source | Lean realization |
|---|---|---|
| Tag alphabet for TM encoding | Cocke-Minsky | `cockeMinskyTagSize := s·k + k + 1` (A/B/C markers) |
| `A(q,a)` state-symbol marker | Cocke-Minsky | `cockeMinskyMarkerA` |
| `B(a)` tape-cell marker | Cocke-Minsky | `cockeMinskyMarkerB` |
| `C` separator | Cocke-Minsky | `cockeMinskyMarkerC` |
| Smith's hierarchy of 6 systems | Smith 2007, §5 | Not formalized; `SmithSimulation : Prop` placeholder |

## Chain DAG

```
                         any TM
                            |
                            | h_cm (Cocke-Minsky 1964)
                            v
                         2-Tag system
                            |
                            | tagToCyclicTagSystemHaltingForward (Cook 2004)
                            |     ← FULLY PROVED, 0 sorry
                            v
                      Cyclic Tag System
                            |
                            | h_smith (Smith 2007)
                            v
                       Wolfram's (2,3) TM
```

## Lemma nodes

### D1 — Cocke-Minsky tag system construction

**Statement.** `cockeMinskyTag machine` constructs a tag system on `s·k+k+1` symbols. Production rules sketch state transitions but the actual binary-tape doubling encoding is *not* in this formalization.
**Lean.** `cockeMinskyTag`, helper markers.
**Status.** Defined (sketch only).
**Basic notions.** A/B/C markers.

### D2 — Cocke-Minsky configuration encoding

**Statement.** `cockeMinskyConfigurationEncode machine config` encodes a TM configuration as `[A(state, head), B(right[0]), …, C, B(left[0]), …]`. Halted configs (state=0) encode to `[]`.
**Lean.** `cockeMinskyConfigurationEncode`.
**Status.** Defined.

### L1 — Halting empty forward (given step simulation)

**Statement.** If a TM halts and the Cocke-Minsky step simulation holds, then the encoded tag word reaches `[]` after finite steps.
**Depends on.** `h_cm`, `tagExactStepsPrependEvaluate`, `cockeMinskyHaltedImpliesTagEmpty`.
**Lean.** `cockeMinskyHaltingEmptyForward`.
**Status.** Proved (modulo `h_cm`).

### L2 — Tag → CTS halting (Cook)

**Statement.** Tag halting (empty word) implies CTS halting on the encoded initial config.
**Lean.** `tagToCyclicTagSystemHaltingForward` (imported from `Proofs.TagSystemToCyclicTagSystem`).
**Status.** **Fully proved** (the only middle step that is sorry-free).

### L3 — TM → CTS composition

**Statement.** Combine L1 + L2: TM halts ⇒ CTS halts on the composed encoding.
**Lean.** `turingMachineToCyclicTagSystem`.
**Status.** Proved (modulo `h_cm`).

### L4 — Smith's CTS → (2,3) TM

**Statement.** Every CTS halting implies (2,3) TM halts on Smith-encoded tape.
**Lean.** `SmithSimulation : Prop` (placeholder); `smithEncode` (placeholder encoder).
**Status.** **Hypothesis only** (`h_smith`).
**Basic notions.** Hierarchy of 6 intermediate systems.

### Edge assembly — `wolfram23Universal` / `edge_CockeMinskyChain`

**Statement.** `IsUniversal wolfram23 := ∀ machine, ∃ encode : Configuration → Configuration, ∀ config, Halts machine config → Halts wolfram23 (encode config)`.
**Lean.** `wolfram23Universal h_cm h_smith` (proof file), `edge_CockeMinskyChain h_cm h_smith` (registered wrapper).
**Status.** **Conditional**: chain composition through L1, L2, L3, L4. Free of internal sorry. The two hypotheses are visible in the type signature.

## Note on the HaltingSimulation form

The proof file also defines `wolfram23HaltingSimulation` which packages this as a `HaltingSimulation`. That packaging contains a buried `sorry` in the `Halts` ↔ `Halts` bridge between `BiInfiniteTuringMachine.Halts` and `ComputationalMachine.Halts`. We do **not** register the HaltingSimulation form as an edge; the universality claim form (`IsUniversal`) is the official registered shape. Resolving the bridge sorry is a separate task.

## See also

- [CockeMinskyChain](../CockeMinskyChain.md) — informal overview
- [Smith2007](../../Resources/Smith2007.md) — the (2,3) TM universality paper
