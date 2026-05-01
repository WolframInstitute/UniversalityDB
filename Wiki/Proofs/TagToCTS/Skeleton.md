# Tag → CTS — Proof Skeleton

Source: **Cook, "Universality in Elementary Cellular Automata"**, *Complex Systems* **15** (2004) 1–40.

## Edge claim

| Lean wrapper | Source | Target | Status |
|---|---|---|---|
| `UniversalityGraph.edge_TagtoCTS` | CyclicTagSystem (Cook encoding of `ts`), 1 tag step = 2k CTS steps | Tag system `ts` (alphabet size `k`) | **conditional** |

Open hypothesis (top-level parameter):

| Hypothesis | Description | Status |
|---|---|---|
| `hHalt : ∀ config, ts.step config = none → CTS.Halts (encode config)` | Halted tag configs encode to halting CTS configs | Empty case is proved (`cyclicTagSystemHaltsOnEmpty`); single-element case is the gap |

## Basic notions

| Notion | Source | Lean realization |
|---|---|---|
| One-hot symbol encoding | Cook §3 | `symbolEncode : Fin k → List Bool`, `true` at position `i` |
| Word encoding | Cook §3 | `tagWordEncode = flatMap symbolEncode` |
| 2k-appendant CTS | Cook §3 | `tagToCyclicTagSystem`: first `k` are productions, second `k` are empty |
| Phase counter | Cook §3 | `CyclicTagSystemConfiguration.phase` mod `2k` |
| Symbol-driven appendant selection | Cook §3 | `currentAppendant (phase + a)` for symbol `a` |

## Lemma DAG

```
   D1 (symbolEncode)              D2 (tagWordEncode)
        \                              /
         \                            /
          L1 (encoding lengths, append distributivity)
                       |
                       v
          L2 (symbolEncodeExactSteps)   ← processes k bits of a one-hot symbol
                       |
                       v
          L3 (tagToCyclicTagSystemSimulation)   ← 2k steps per tag step
                       |
                ┌──────┴───────┐
                v              v
         L4 (haltingForward)   L5 (haltingBackward)
                |              |
                └──────┬───────┘
                       v
              E_TagtoCTS (registered edge)
                       ↑
                       hHalt hypothesis (single-element gap)
```

## Lemma nodes

### D1 — symbol encoding

**Statement.** `symbolEncode k i = (range k).map (j ↦ j == i.val)`.
**Lean.** `symbolEncode`, length lemma `symbolEncodeLength`.
**Status.** Proved.

### D2 — word encoding

**Statement.** `tagWordEncode k word = word.flatMap (symbolEncode k)`.
**Lean.** `tagWordEncode`, lemmas `tagWordEncodeLength`, `tagWordEncodeAppend`.
**Status.** Proved.

### L1 — phase arithmetic

**Statement.** Phase advances by `len` correspond to mod-`2k` arithmetic on the phase counter.
**Lean.** `phaseSuccMod`, `phaseAppMod`, `mapRangeSucc`.
**Status.** Proved.

### L2 — symbolEncodeExactSteps

**Statement.** Starting at phase `p` with data `symbolEncode k a ++ tail`, after `k` CTS steps data becomes `tail ++ currentAppendant(p + a)` and phase becomes `(p + k) mod 2k`.
**Depends on.** L1.
**Lean.** `symbolEncodeExactSteps`, helper `symbolEncodeExactStepsHelper`.
**Status.** Proved.
**Basic notions.** One-hot symbol encoding, phase counter.

### L3 — tagToCyclicTagSystemSimulation (2k step lemma)

**Statement.** For tag step on `a :: b :: rest → rest ++ productions(a)`, the 2k-step CTS evolution from `tagConfigurationToCyclicTagSystem k (a::b::rest)` reaches `tagConfigurationToCyclicTagSystem k (rest ++ productions a)`.
**Depends on.** L2, appendant lemmas (`tagToCyclicTagSystemAppendantFirst`/`Second`).
**Lean.** `tagToCyclicTagSystemSimulation`.
**Status.** Proved.
**Basic notions.** 2k-appendant CTS.

### L4 — Halting forward

**Statement.** If the tag system reaches the empty word, the CTS halts on the encoded initial config.
**Depends on.** L3.
**Lean.** `tagToCyclicTagSystemHaltingForward`.
**Status.** Proved.

### L5 — Halting backward

**Statement.** If the CTS halts on the encoded initial config, the tag system also halts.
**Depends on.** L3, length-bound `cyclicTagSystemEvaluateNoneOfLength`.
**Lean.** `cyclicTagSystemToTagHalting`.
**Status.** Proved.

### Halting field gap (`hHalt`)

`Tag.step = none` ↔ word length < 2. Two sub-cases:
- **Length 0**: encoded as `[]`, CTS halts immediately. **Proved** (`cyclicTagSystemHaltsOnEmpty`).
- **Length 1**: encoded as `k` bits. The CTS *only* halts on this configuration when `productions a = []` (after `k` steps the data drains); when `productions a` is non-empty, the CTS keeps simulating Cook's encoding on the production word and may never halt. There is no in-Lean discharge of this case for arbitrary tag systems — it is a property of the specific tag system being encoded.

The wrapper `edge_TagtoCTS` exposes this as the explicit hypothesis `hHalt : ∀ cfg, ts.step cfg = none → CTS.Halts (encode cfg)`. For tag systems built via Cocke-Minsky from a TM, `hHalt` is satisfied because such tag systems are constructed to halt only via the empty word.

## See also

- [TagToCTS](../TagToCTS.md) — informal overview
- [Cook2004](../../Resources/Cook2004.md) — the paper
