# Tag System

> Status: **draft**

A tag system operates on a finite word over an alphabet of size k. At each step it reads the first symbol, appends the corresponding production word to the end, and deletes the first 2 symbols (for a 2-tag system). Halts when the word length drops below 2.

## Lean formalization

`Lean/Machines/TagSystem/Defs.lean`

`Tag (alphabetSize)` has a production function mapping each symbol to a word. `TagConfiguration` is a `List (Fin alphabetSize)`. Key lemmas: `evaluateStep`, `stepNoneIffHalted`, `evaluateAdd`.

## Universality edges

- TM → 2-Tag (Cocke-Minsky 1964): tag alphabet = s*k + k + 1. See [[CockeMinskyChain]].
- 2-Tag → Cyclic Tag (Cook 2004): one-hot encoding, 1 tag step = 2k CTS steps. See [[TagToCTS]].

## See also

- [[CyclicTagSystem]] — the binary simplification
- [[CockeMinskyChain]] — the full reduction chain
