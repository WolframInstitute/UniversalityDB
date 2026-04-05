# TM → Generalized Shift (Moore Theorem 7)

> Status: **draft**

Any Turing machine can be simulated by a generalized shift with σ=1, τ=1 (a bisimulation).

## Encoding

The TM state is merged into the tape cell at the head position. The extended alphabet has size s*k + k, where s = number of states, k = number of symbols. The first k symbols are "passive" (no state), the remaining s*k encode (state, color) pairs. The GS has windowWidth=3: [left neighbor, active cell, right neighbor].

## Lean formalization

`Lean/Proofs/TuringMachineToGeneralizedShift.lean`

Key definitions: `encodeActive`/`decodeActive` (state-into-tape), `encodeBiTM`/`decodeBiTM` (full config), `fromBiTM` (construct GS from TM).

Key theorems:
- `decodeActiveEncodeActive` — alphabet roundtrip
- `decodeEncode` — config roundtrip (nonempty tapes)
- `stepCommutes` — one TM step = one GS step
- `stepCommutesNorm` — up to tape normalization
- `mooreHaltingForward` — halting preservation

**Status:** 0 sorry. Fully proved.

## See also

- [[GStoTM]] — the reverse direction (Moore Theorem 8)
- [[TuringMachine]], [[GeneralizedShift]] — the systems
- [[Moore1991]] — the paper
