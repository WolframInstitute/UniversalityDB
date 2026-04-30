# TM ↔ Generalized Shift (Moore 1991)

Moore's Theorem 7: any Turing machine is conjugate to a generalized shift via state-into-tape encoding. Bisimulation with σ = 1, τ = 1.

Reference: C. Moore, *Generalized shifts: unpredictability and undecidability in dynamical systems*, Nonlinearity 4 (1991) 199-230.

## Setup

```wolfram
SetEnvironment[ "PATH" -> Environment[ "PATH" ] <> ":" <> FileNameJoin[ { $HomeDirectory, ".elan", "bin" } ] ];
PacletDirectoryLoad[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "LeanLink", "LeanLink" } ] ];
Get[ "LeanLink`" ];
leanProjectDir = FileNameJoin[ { NotebookDirectory[], "..", "Lean" } ];
gs = ResourceFunction[ "GeneralizedShift" ];
```

## 1. Machine Definitions

**Bi-infinite Turing Machine (BiTM)** — state in {0, ..., s}, symbols in {0, ..., k-1}, state 0 = halted. Source: `Resources/TuringMachine/Proofs/BiTM/Basic.lean`.

**Generalized Shift** — stateless dynamical system on a bi-infinite tape with a 3-cell window. The active cell (value ≥ k) encodes head position + state. Source: `Lean/Machines/GeneralizedShift/Defs.lean`.

## 2. Encoding

Moore's state-into-tape encoding merges the TM state into the cell at the head position. Extended alphabet of size `s*k + k`: plain cells `0..k-1`, active cells `A(q, c) = k + (q-1)*k + c`. Source: `Lean/Proofs/TuringMachineToGeneralizedShift.lean`.

The TM → GS edge is a thin wrapper that bridges Moore's exact step to a normalized step (`stepNormalized` post-strips trailing zeros from both tapes), so the conjugation reads strictly: `step_BiTM(b) = decode (step_GS^n (encode b))`, no `modulo normalize` qualifier. Source: `Lean/Proofs/TMtoGS.lean`.

## 3. Validation

Define a 2-state 2-color TM and run the equivalent generalized shift. `ResourceFunction["GeneralizedShift"]` converts TM rules to a GS spec and evolves it using Moore's encoding internally.

```wolfram
tmRules = { {1, 0} -> {2, 1, 1}, {1, 1} -> {1, 1, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 0, 1} };
nSteps = 30;
```

```wolfram
gsSpec = gs[ tmRules ];
gsResult = gs[ gsSpec, { { 0, 0, 0 }, 1 }, nSteps ];
```

```wolfram
ArrayPlot[ gsResult[[ All, 2 ]], Frame -> False, ImageSize -> 600, PlotLabel -> "GS evolution (active cell encodes TM state)" ]
```

## 4. Lean Verification

> A successful `LeanImportString` (no error returned) means Lean's kernel has accepted every definition and proof in the file. If this cell fails, no theorem below can be trusted.

```wolfram
env = LeanImportString[ Import[ FileNameJoin[ { leanProjectDir, "Proofs", "TMtoGS.lean" } ], "Text" ], "ProjectDir" -> leanProjectDir ];
Length[ Keys[ env ] ]
```

### Main theorem

The theorem `TMtoGS.tmToGSSimulation` returns a `ComputationalMachine.SimulationEncoding` whose `commutes` field is the conjugation `step_BiTM(b) = decode (step_GS^n (encode b))`.

> Read the type below. Any extra hypothesis weakens the claim — verify the only hypotheses are the four well-formedness conditions (`_hk`, `_hHeadAll`, `_hWriteBound`, `_hStateBound`).

```wolfram
env[ "TMtoGS.tmToGSSimulation" ][ "TypeForm" ]
```
