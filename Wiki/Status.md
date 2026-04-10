# Project Status

Last updated: 2026-04-10

## Proved edges (0 sorry)

| Edge | File | Overhead |
|---|---|---|
| TM → GS (Moore Thm 7) | `Lean/Proofs/TuringMachineToGeneralizedShift.lean` | σ=1, τ=1 |
| GS → TM (Moore Thm 8) | `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | σ=1, τ≤2(w-1)+m (w=1 fully proved; general w wired, 1 sorry in composition) |
| Tag → CyclicTag | `Lean/Proofs/TagSystemToCyclicTagSystem.lean` | 1 tag step = 2k CTS steps |
| ECA Rule 110 ↔ Rule 124 | `Lean/Proofs/ElementaryCellularAutomatonMirror.lean` | σ=1, τ=1 (tape reversal) |

## Hypothetical edges (stated as explicit hypotheses, not axioms)

| Edge | File | Hypothesis | Statement |
|---|---|---|---|
| TM → 2-Tag (Cocke-Minsky) | `Lean/Proofs/CockeMinsky.lean:179` | `CockeMinskyStepSimulation` | For every TM and every step `config → config'`, there exist bounded tag steps mapping `encode(config)` to `encode(config')` |
| CTS → (2,3) TM (Smith) | `Lean/Proofs/CockeMinsky.lean:336` | `SmithSimulation` | For every CTS and config, if the CTS halts, then `wolfram23` halts on the Smith-encoded tape |

These are `def` declarations appearing as parameters in theorem type signatures, not `axiom` declarations. Every theorem that depends on them states the dependency explicitly.

## Main theorem

`wolfram23Universal` in `Lean/Proofs/CockeMinsky.lean`: Wolfram's (2,3) TM is universal, assuming `CockeMinskyStepSimulation` and `SmithSimulation`.

## Proof integrity

Run `Scripts/verify_integrity.sh` to verify. The script uses `CollectAxioms.collect` on every key theorem to check axiom dependencies, `leanchecker` for full kernel replay, and validates that `Integrity.lean` imports match `lakefile.lean` roots. See [ProofIntegrity](Concepts/ProofIntegrity.md) for the full trust model.

### Sorry inventory

| File | Line | Theorem | Reason |
|---|---|---|---|
| `Lean/Proofs/GeneralizedShiftToTuringMachine.lean` | 1314 | `fullSim_general` | All 4 phase building blocks proved (readScan, biTM_step_lastRead, writeLoop, writeZeroShift). Final composition through all phases deferred. Width-1 fully proved via `stepSimulation_w1`. |

Total: **1 sorry**.

### native_decide inventory

All uses are concrete evaluations on specific inputs — no universal claims.

| File | Theorem | What it checks |
|---|---|---|
| `Machines/BiInfiniteTuringMachine/Defs.lean:92` | `wolfram23Step1` | Single step of wolfram23 on specific input |
| `Machines/BiInfiniteTuringMachine/Defs.lean:97` | `wolfram23Step2` | 2-step execution on specific input |
| `Machines/BiInfiniteTuringMachine/Defs.lean:101` | `wolfram23Runs10` | 10-step non-halting check |
| `Machines/BiInfiniteTuringMachine/Defs.lean:105` | `wolfram23Runs20` | 20-step non-halting check |
| `Machines/TagSystem/Defs.lean:177` | `exampleCyclicTagSystemStep1` | Single CTS step on 2-bit input |
| `Machines/TagSystem/Defs.lean:182` | `exampleCyclicTagSystemStep2` | Two CTS steps composed |
| `Proofs/TagSystemToCyclicTagSystem.lean:532` | `symbolEncode20` | One-hot encoding of symbol 0 |
| `Proofs/TagSystemToCyclicTagSystem.lean:533` | `symbolEncode21` | One-hot encoding of symbol 1 |
| `Proofs/TagSystemToCyclicTagSystem.lean:537` | `tagWordEncode01` | Word encoding `[0,1]` → binary |
| `Proofs/TagSystemToCyclicTagSystem.lean:542` | `tagToCyclicTagSystemAppendants` | CTS appendants match expected |
| `Proofs/TagSystemToCyclicTagSystem.lean:562` | `simulationExampleCorrected` | 4 CTS steps on encoded `[0,1,0]` |
| `Proofs/TagSystemToCyclicTagSystem.lean:569` | `simulationExample2` | 4 CTS steps on encoded `[1,0,1]` |
| `Proofs/TagSystemToCyclicTagSystem.lean:576` | `simulationExample3` | 4 CTS steps on encoded `[0,0,1,1]` |

### decide inventory (kernel-verified)

| File | Theorem | What it checks |
|---|---|---|
| `Proofs/ElementaryCellularAutomatonMirror.lean:16` | `mirrorProperty` | `rule110(a,b,c) = rule124(c,b,a)` for all `a, b, c : Fin 2` (8 cases) |

This finite check bootstraps a universal result via structural induction in `mirrorSimulationGeneral` and `mirrorSimulationSteps`.

## Machine families in Lean

- Turing Machine (one-sided): `Lean/Machines/TuringMachine/Defs.lean`
- Bi-infinite Turing Machine: `Lean/Machines/BiInfiniteTuringMachine/Defs.lean`
- Generalized Shift: `Lean/Machines/GeneralizedShift/Defs.lean`
- 2-Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Cyclic Tag System: `Lean/Machines/TagSystem/Defs.lean`
- Elementary Cellular Automaton: `Lean/Machines/ElementaryCellularAutomaton/Defs.lean`

## Overhead formalization

Overhead bounds are proved per-edge as standalone theorems but **not yet bundled** into `Overhead` records or `SimulationEncoding` instances. Packaging them would enable formal composition via `Overhead.compose`.

## Current focus

GS → TM general width: all building blocks fully proved (readScan, lastRead, writeLoop, writeZeroShift — 0 sorry). One sorry remains in `fullSim_general` — the composition that chains the 4 phases via `exactSteps_append`. See `Wiki/Plans/GStoTM_GeneralWidth.md`.

## See also

- [CockeMinskyChain](Proofs/CockeMinskyChain.md) — the full TM → Tag → CTS → (2,3) TM chain
- [SimulationEncoding](Concepts/SimulationEncoding.md) — the core Lean abstraction
- [ProofIntegrity](Concepts/ProofIntegrity.md) — trust model and verification procedures
