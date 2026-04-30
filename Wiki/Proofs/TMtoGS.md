# TM → Generalized Shift (Moore Theorem 7)

Any Turing machine is conjugate to a generalized shift, with overhead σ=1, τ=1.

## Encoding

The TM state is merged into the tape cell at the head position. Extended alphabet has size `s·k + k`, where `s` = states, `k` = symbols. The first k symbols are "passive" (no state); the remaining s·k encode `(state, color)` pairs. The GS has `windowWidth=3`: [left neighbor, active cell, right neighbor].

## Lean formalization

Building blocks: [Lean/Proofs/TuringMachineToGeneralizedShift.lean](../../Lean/Proofs/TuringMachineToGeneralizedShift.lean)

- `encodeActive` / `decodeActive` — state-into-tape on the alphabet
- `encodeBiTM` / `decodeBiTM` — full configuration
- `fromBiTM` — construct GS from TM
- `decodeActiveEncodeActive` — alphabet roundtrip
- `decodeEncode` — configuration roundtrip (nonempty tapes)
- `stepCommutes` — strict-equality TM↔GS step (nonempty tapes)
- `stepCommutesNorm` — equality up to tape normalization
- `normalize` (with `normalize_cons_congr`, `headD_normalize`, `tail_normalize`, idempotency) — list-level trailing-zero stripping

Edge proof: [Lean/Proofs/TMtoGS.lean](../../Lean/Proofs/TMtoGS.lean)

- `biTMStepUniform` / `biTMStep_eq_uniform` — `headD`/`tail` reformulation of BiTM step (avoids case-split explosion)
- `normalizeBiTMConfig` / `decodeBiTMNormalized` — BiTM-side decoder helpers
- `normalize_eq_stripTrailingZeros` / `normalizeBiTMConfig_eq_stripConfig` — bridge to BiTM canonical form (one-line proofs since the two normalizers are literally identical bodies in different namespaces)
- `decodeBiTMNormalized_encode_eq` — decoding-then-normalizing the encoding recovers the canonical form
- `tmToGSCommutesMoore` — the core commutation theorem against Moore's exact step
- `tmToGSSimulation` — thin wrapper returning `ComputationalMachine.SimulationEncoding`, against `BiInfiniteTuringMachine.toComputationalMachineNormalized`

The wrapper `edge_TMtoGS` lives in [Lean/Edges.lean](../../Lean/Edges.lean).

**Status.** 0 sorry. Axiom closure: `[propext, Quot.sound, Classical.choice]`. Conditional only on four well-formedness hypotheses on the machine (`hk`, `hHeadAll`, `hWriteBound`, `hStateBound`).

## See also

- [GStoTM](GStoTM.md) — the reverse direction (Moore Theorem 8)
- [TuringMachine](../Systems/TuringMachine.md), [GeneralizedShift](../Systems/GeneralizedShift.md) — the systems
- [SimulationEncoding](../Concepts/SimulationEncoding.md) — the structure form used here
- [Moore1991](../Resources/Moore1991.md) — the paper
- [Skeleton](TMtoGS/Skeleton.md) — paper-driven layered DAG
