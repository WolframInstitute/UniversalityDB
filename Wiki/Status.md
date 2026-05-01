# Project Status

Last updated: 2026-05-01

## Simulation framework

`Lean/SimulationEncoding.lean` defines three templates in increasing strength:
`HaltingSimulation`, `Simulation`, `SimulationEncoding`. `Simulation` is used by
4 edges (canonical, composable); `SimulationEncoding` (the conjugation form) is
used by 1 edge (TM → GS); `HaltingSimulation` is used by `wolfram23HaltingSimulation`.

The dead-code `SimulationViaDecode` (with `roundtrip + normalize` fields) was
removed in favor of `SimulationEncoding`, which carries pure conjugation:
`step_B(b) = decode (step_A^n (encode b))`. Canonicalization, when needed, is
on the *machine* via `stepNormalized` plus a bisimulation lemma — not as a
structure field.

Every machine family has a `toComputationalMachine` wrapper in its `Defs.lean`.
Bi-infinite-tape machines also expose a `stepNormalized` /
`toComputationalMachineNormalized` variant that post-strips trailing zeros from
both tapes (`Lean/Machines/GeneralizedShift/Defs.lean`,
`Lean/Machines/BiInfiniteTuringMachine/Defs.lean`). The TM → GS edge targets
the normalized BiTM, which is what makes the conjugation in `SimulationEncoding`
strict (no `modulo normalize`).

`BiInfiniteTuringMachine.step_stripConfig_bisim` proves the bisimulation
`(step c).map stripConfig = stepNormalized (stripConfig c)` — i.e., the
standard `step` is well-defined modulo trailing-zero canonicalization. The
analogous lemma for `GeneralizedShift.step` is structurally similar
(induction over `shiftBy` with single-step bisimulations on
`shiftRightOne`/`shiftLeftOne`); `stripConfig_idempotent` is proved and the
chain is documented in-file. Lean formalization of the GS shift bisim is
deferred — paper-and-pencil-clear, tedious case analysis (cells × right tape
× left tape branches).

## Proved edges

| Edge | File | Template | Overhead | Sorry in proof |
|---|---|---|---|---|
| TM → GS (Moore Thm 7) | `Lean/Proofs/TMtoGS.lean` | `SimulationEncoding` (conjugation) | σ=1, τ=1 | 0 (4 well-formedness hypotheses) |
| GS → TM (Moore Thm 8) | `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | `SimulationEncoding` (conjugation) | σ=1, τ≤2(w-1)+m | 0 (7 well-formedness hypotheses) |
| Tag → CyclicTag (Cook 2004) | `Lean/Proofs/TagSystemToCyclicTagSystem.lean` | `Simulation` | 1 tag step = 2k CTS steps | 0 (singleton-halting taken as edge hypothesis `hHalt`) |
| ECA Rule 110 ↔ Rule 124 | `Lean/Proofs/ElementaryCellularAutomatonKleinGroup.lean` | `Simulation` | σ=1, τ=1 | 0 |
| ECA Rule 110 ↔ Rule 137 (complement) | `Lean/Proofs/ElementaryCellularAutomatonKleinGroup.lean` | `Simulation` | σ=1, τ=1 | 0 |
| ECA Rule 110 ↔ Rule 193 (mirror ∘ complement) | `Lean/Proofs/ElementaryCellularAutomatonKleinGroup.lean` | `Simulation` | σ=1, τ=1 | 0 |

## Hypothetical edges (stated as hypotheses)

| Edge | File | Hypothesis |
|---|---|---|
| TM → 2-Tag (Cocke-Minsky 1964) | `Lean/Proofs/CockeMinsky.lean` | `CockeMinskyStepSimulation`: every TM step lifts to bounded tag steps |
| CTS → (2,3) TM (Smith 2007) | `Lean/Proofs/CockeMinsky.lean` | `SmithSimulation`: every CTS computation is tracked by the (2,3) TM |

## Main theorem

`wolfram23Universal` in `Lean/Proofs/CockeMinsky.lean`: Wolfram's (2,3) TM is universal, assuming CockeMinsky and Smith hypotheses.

`wolfram23HaltingSimulation`: same result wrapped as a `HaltingSimulation` instance (1 sorry bridging `ComputationalMachine.Halts` ↔ `BiInfiniteTuringMachine.Halts`).

## Proof integrity

Run `Scripts/verify_integrity.sh` to verify. The script uses `CollectAxioms.collect` on every key theorem to check axiom dependencies, `leanchecker` for full kernel replay, and validates that `Integrity.lean` imports match `lakefile.lean` roots. See [ProofIntegrity](Concepts/ProofIntegrity.md) for the full trust model.

## Edge registry

[Lean/Edges.lean](../Lean/Edges.lean) contains the registered edges as named typed wrappers; [Lean/EdgeAudit.lean](../Lean/EdgeAudit.lean) prints an audit trail at build time (machines, paper ref, hypothesis list, axiom closure). **Ten** edges registered (`EDGE AUDIT: PASS (10 edges)` at build time):

| Edge | Status | Top-level hypotheses | Wrapper axioms |
|---|---|---|---|
| `edge_ECA110_ECA124` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA124_ECA110` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA110_ECA137` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA137_ECA110` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA110_ECA193` | unconditional | (none) | propext, Quot.sound |
| `edge_ECA193_ECA110` | unconditional | (none) | propext, Quot.sound |
| `edge_TMtoGS` | conditional (4 well-formedness assumptions) | hk, hHeadAll, hWriteBound, hStateBound — **commutes and halting fully proved** | propext, Quot.sound, Classical.choice |
| `edge_GStoTM` | conditional (7 well-formedness assumptions) | hAlpha, hWidth, hLen, hShift, hRepl, hCellBoundAll, hHalt — **commutes and halting fully proved** | propext, Quot.sound, Classical.choice |
| `edge_TagtoCTS` | conditional | `hHalt` (single-element tag word case) | propext, Quot.sound, Classical.choice |
| `edge_CockeMinskyChain` | conditional | `h_cm`, `h_smith` | propext, Quot.sound, Classical.choice |

All wrapper closures are sorry-free. The remaining buried sorry in the proof files (`wolfram23PreservesHalting` bridge) is excluded from the wrapper closures because the wrappers hoist the missing piece to a top-level `Prop` parameter. The earlier `tagToCTSSimulation` sorry has been retired by removing the dead reference definition: `edge_TagtoCTS` already constructs the simulation directly via `tagToCTSCommutes` plus the explicit `hHalt` hypothesis, so no sorry is needed.

Per-proof paper-driven skeletons under [Wiki/Proofs/<Name>/Skeleton.md](Proofs/) — see the [VerificationFramework](Plans/VerificationFramework.md) plan.

## Machine families in Lean

Each family has a `toComputationalMachine` wrapper and an `iterationStep_eq_exactSteps` compatibility lemma.

- Turing Machine (one-sided): `Lean/Machines/TuringMachine/Defs.lean`
- Bi-infinite Turing Machine: `Lean/Machines/BiInfiniteTuringMachine/Defs.lean`
- Generalized Shift: `Lean/Machines/GeneralizedShift/Defs.lean`
- 2-Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Cyclic Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Elementary Cellular Automaton: `Lean/Machines/ElementaryCellularAutomaton/Defs.lean`

## Simulation framework

`Lean/SimulationEncoding.lean` defines three templates:

| Structure | Fields | Use |
|---|---|---|
| `HaltingSimulation A B` | `encode`, `preserves_halting` | Halting preservation only (e.g. Smith) |
| `Simulation A B` | `encode`, `commutes`, `halting` | Canonical step-level simulation (4 edges). Composes. |
| `SimulationEncoding A B` | `encode`, `decode`, `commutes`, `halting` | Conjugation form `step_B = decode ∘ step_A^n ∘ encode` (TM→GS) |

`Simulation` composes via `Simulation.compose` and derives `halting_preserved`. `HaltingSimulation` composes via `HaltingSimulation.compose`. `SimulationEncoding` is a presentation form for edges with a natural decode; it doesn't compose (and doesn't need to — composition flows through `Simulation`).

## Current focus

GS → TM SimulationEncoding (Moore Thm 8 conjugation form) — **completed 2026-05-01**.

**Done:**
- `writeLoop` reformulated to k steps from writeState(k) (uniform; no w=2 vs w≥3 split).
- Helper lemmas `chain_left_form`, `chain_getLastD` (~25 lines).
- **`fullSim_general_cView` fully discharged** (no sorry, empty axiom closure). The chain reads: encodeConfig → readScan + lastRead + writeLoop + writeZeroShift, landing at the [c]-view of the shift target.
- `decodeConfigPadded` defined (pads cells with 0 to width w when right tape underflows).
- Static bridge `decodeConfigPadded_encodeConfig` proved.
- **Per-step bridge `decodePadded_shiftRightOne`** (unconditional) — proved using helper lemmas `shiftRightOne_singleton_{nil,cons}` plus list-arithmetic case analysis on `rs.drop k'`. Uses `List.dropLast_concat` / `List.getLastD_concat` to reduce structure.
- **Per-step bridge `decodePadded_shiftLeftOne`** (with precondition `right.length ≥ w-1`) — clean proof via `decodePadded_proper_form` helper, which exposes the no-padding form of decoded config. The precondition is preserved by shiftLeft (which only grows the right tape), so it propagates through the `shiftBy mag true` induction.
- **Full bridges `decodePadded_shiftByRight` / `decodePadded_shiftByLeft`** — induction on mag using per-step bridges + `Option.map_map`.
- **`replAsc_eq_tail`** — proved via helper `replAsc_cons_eq_take`, by induction on k.
- **`gsToTMSimulationEncoding.commutes` fully proved** — combines chain + bridge. Branches on w=1 (uses `fullSim_w1` + bridges + `decodePadded_proper_form`) vs w≥2 (uses `fullSim_general_cView` + bridges + `replAsc_eq_tail`).
- `edge_GStoTM` registered as `SimulationEncoding`. Closure: `[propext, Quot.sound, Classical.choice]`.

See `Wiki/Plans/GStoTM_SimulationEncoding.md` History for the full implementation log.

## See also

- [CockeMinskyChain](Proofs/CockeMinskyChain.md) — the full TM → Tag → CTS → (2,3) TM chain
- [SimulationEncoding](Concepts/SimulationEncoding.md) — the core Lean abstraction
- [ProofIntegrity](Concepts/ProofIntegrity.md) — trust model and verification procedures
