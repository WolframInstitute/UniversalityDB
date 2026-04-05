# Cyclic Tag System

> Status: **draft**

A cyclic tag system (CTS) operates on a binary word. It cycles through a fixed list of appendant words. At each step: remove the first bit; if it was 1, append the current appendant. Advance the phase counter (mod number of appendants). Halts when the word is empty.

## Lean formalization

`Lean/Machines/TagSystem/Defs.lean` (same file as 2-tag systems)

`CyclicTagSystem` has a list of appendants (with a nonemptiness proof). `CyclicTagSystemConfiguration` = (data : List Bool, phase : Nat). `currentAppendant` indexes by phase mod length.

## Universality edges

- 2-Tag → CTS (Cook 2004): one-hot symbol encoding, 2k appendants. Fully proved. See [[TagToCTS]].
- CTS → (2,3) TM (Smith 2007): hypothesis in current formalization. See [[CockeMinskyChain]].

## See also

- [[TagSystem]] — the more general model
- [[Cook2004]] — universality of Rule 110 via CTS
