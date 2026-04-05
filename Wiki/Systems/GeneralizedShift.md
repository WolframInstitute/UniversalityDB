# Generalized Shift

> Status: **draft**

Introduced by Moore (1991) as a dynamical systems model equivalent to Turing machines. A generalized shift operates on a bi-infinite tape by reading a window of w cells, replacing the window contents, and shifting the window by some magnitude in a given direction.

## Definition

A generalized shift has:
- Alphabet size n
- Window width w
- Transition function: window contents → (replacement, shift magnitude, shift direction)
- Activity predicate: which windows trigger a step (inactive = halted)

## Lean formalization

`Lean/Machines/GeneralizedShift/Defs.lean`

Key types: `ShiftRule` (replacement + magnitude + direction), `Machine`, `Configuration` (left, cells, right). Helper functions `shiftRightOne`, `shiftLeftOne`, `shiftBy` implement window movement.

## Universality edges

- TM → GS (Moore Thm 7): state-into-tape encoding with windowWidth=3. σ=1, τ=1. See [[TMtoGS]].
- GS → TM (Moore Thm 8): three-phase TM (read/write/shift). σ=1, τ≤2(w-1)+m. See [[GStoTM]].

## See also

- [[TuringMachine]] — equivalent model
- [[Moore1991]] — the original paper
