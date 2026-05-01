# 2-Tag System → Cyclic Tag System (Cook 2004)

Cook's encoding reduces any 2-tag system to a cyclic tag system. This is the fully proved middle link in the Cocke-Minsky chain.

## Encoding

Each symbol i in a k-letter tag alphabet is encoded as a one-hot binary word of length k (1 at position i, 0 elsewhere). The CTS has 2k appendants: the first k encode the tag productions (one-hot), the next k are empty. One tag step (delete 2, append production) corresponds to exactly 2k CTS steps.

## Lean formalization

`Lean/Proofs/TagSystemToCyclicTagSystem.lean`

Key definitions: `symbolEncode`, `tagWordEncode`, `tagToCyclicTagSystem`, `tagConfigurationToCyclicTagSystem`.

Key theorems:
- `tagToCyclicTagSystemSimulation` — 1 tag step = 2k CTS steps
- `tagToCyclicTagSystemHaltingForward` — tag halts → CTS halts
- `cyclicTagSystemToTagHalting` — CTS halts → tag halts (backward direction)

**Status:** 0 sorry in proof file. The edge wrapper `edge_TagtoCTS` is conditional on a single hypothesis `hHalt : ∀ cfg, ts.step cfg = none → CTS.Halts (encode cfg)`. This covers the single-element case `[a]`: Cook's encoding only halts on `encode [a]` when `productions a = []`, so the conditionality is real and is exposed at the top level rather than hidden behind a sorry.

## See also

- [CockeMinskyChain](CockeMinskyChain.md) — the full TM → (2,3) TM chain
- [TagSystem](../Systems/TagSystem.md), [CyclicTagSystem](../Systems/CyclicTagSystem.md) — the systems
- [Cook2004](../Resources/Cook2004.md) — Rule 110 universality (uses this encoding)
