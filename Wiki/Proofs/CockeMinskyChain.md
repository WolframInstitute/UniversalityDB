# Cocke-Minsky Chain: TM → Tag → CTS → (2,3) TM

> Status: **draft**

The central universality chain proving Wolfram's (2,3) Turing machine is computationally universal. The chain composes three simulation encodings.

## The chain

1. **TM → 2-Tag** (Cocke-Minsky 1964): Tag alphabet size = s*k + k + 1. Markers A(q,a) encode state-symbol pairs, B(a) encode tape cells, C is a separator. One TM step maps to a bounded number of tag steps. Currently a hypothesis (`CockeMinskyStepSimulation`).

2. **2-Tag → CTS** (Cook 2004): One-hot binary encoding. 2k appendants. 1 tag step = 2k CTS steps. **Fully proved** — see [[TagToCTS]].

3. **CTS → (2,3) TM** (Smith 2007): Smith's 6-level simulation hierarchy. Currently a hypothesis (`SmithSimulation`).

## Lean formalization

`Lean/Proofs/CockeMinsky.lean`

The main theorem `wolfram23Universal` states: given `CockeMinskyStepSimulation` and `SmithSimulation`, any TM can be simulated by `wolfram23` (the (2,3) machine defined in `Lean/Machines/BiInfiniteTuringMachine/Defs.lean`).

Halting correspondence (`cockeMinskyHaltingForward`, `cockeMinskyHaltedImpliesTagHalted`) is fully proved assuming the step simulation hypothesis.

## See also

- [[TagToCTS]] — the fully proved middle link
- [[TuringMachine]], [[TagSystem]], [[CyclicTagSystem]] — the systems
- [[Smith2007]], [[Cook2004]] — the papers
