# Smith 2007 — Universality of the (2,3) TM

Alex Smith. *Universality of Wolfram's 2,3 Turing Machine.* Wolfram Science Prize submission, 2007.

## Summary

Proves that the (2,3) Turing machine (2 states, 3 colors) is computationally universal by constructing a simulation chain: generic TM → cyclic tag system → Rule 110 → (2,3) TM. Uses a 6-level hierarchy of intermediate systems.

## Key results

- The smallest known universal Turing machine (by state-symbol product).
- Simulation has exponential overhead due to the reduction chain.
- Builds on Cook's Rule 110 universality.

## Recover

Download: https://www.wolframscience.com/prizes/tm23/TM23Proof.pdf
Target: Resources/Smith2007.pdf

## Use in this project

The CTS → (2,3) TM simulation (`SmithSimulation`) is currently a hypothesis in `Lean/Proofs/CockeMinsky.lean`. The main theorem `wolfram23Universal` assumes it.

## See also

- [[CockeMinskyChain]] — the full chain using Smith's result
- [[TuringMachine]] — includes `wolfram23` definition
- [[Cook2004]] — the Rule 110 result Smith builds on
