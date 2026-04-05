# Moore 1991 — Generalized Shifts

Cristopher Moore. *Generalized Shifts: Unpredictability and Undecidability in Dynamical Systems.* Nonlinearity 4, 199-230, 1991.

## Summary

Introduces generalized shifts as a dynamical systems model and proves their equivalence to Turing machines. The key insight is that computation can be characterized as data-dependent shifting on a symbol sequence, bridging discrete computation and continuous dynamical systems.

## Key results

- **Theorem 7:** Any TM is conjugate to a generalized shift via state-into-tape encoding. Extended alphabet size = s*k + k, windowWidth = 3. Overhead: σ=1, τ=1.
- **Theorem 8:** Any generalized shift can be simulated by a TM. Three-phase construction (read/write/shift). Overhead: σ=1, τ = O(w) where w = window width.

## Recover

Download: https://doi.org/10.1088/0951-7715/4/2/002
Target: Resources/Moore1991.pdf

## Use in this project

Both theorems are formalized in Lean. Theorem 7 is fully proved (0 sorry). Theorem 8 has 1 sorry remaining in the step simulation.

## See also

- [TMtoGS](../Proofs/TMtoGS.md), [GStoTM](../Proofs/GStoTM.md) — the formalizations
- [GeneralizedShift](../Systems/GeneralizedShift.md) — the system
