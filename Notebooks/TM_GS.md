# TM ↔ Generalized Shift (Moore 1991)

Moore's Theorem 7: any Turing machine is conjugate to a generalized shift via state-into-tape encoding. Bisimulation with σ = 1, τ = 1.

Reference: C. Moore, *Generalized shifts: unpredictability and undecidability in dynamical systems*, Nonlinearity 4 (1991) 199-230.

## Setup

```wolfram
SetEnvironment[ "PATH" -> Environment[ "PATH" ] <> ":" <> FileNameJoin[ { $HomeDirectory, ".elan", "bin" } ] ]
PacletDirectoryLoad[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "LeanLink", "LeanLink" } ] ];
Get[ "LeanLink`" ]
leanProjectDir = FileNameJoin[ { NotebookDirectory[], "..", "Lean" } ]
gs = ResourceFunction[ "GeneralizedShift" ]
```

## 1. Machine Definitions

### Turing Machine (BiTM)

Bi-infinite tape TM: state in {0, ..., s}, symbols in {0, ..., k-1}, state 0 = halted.

```wolfram
Import[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "TuringMachine", "Proofs", "BiTM", "Basic.lean" } ], "Text" ] // Style[ #, "Code" ] &
```

### Generalized Shift

Stateless machine on a bi-infinite tape. The active cell (value ≥ k) encodes the head position and state.

```wolfram
Import[ FileNameJoin[ { leanProjectDir, "Machine", "GS", "Defs.lean" } ], "Text" ] // Style[ #, "Code" ] &
```

## 2. Encoding

Moore's encoding merges the TM state into the tape cell at the head position. Extended alphabet of size s*k + k: plain cells 0..k-1, active cells A(q, c) = k + (q-1)*k + c.

```wolfram
Import[ FileNameJoin[ { leanProjectDir, "Proof", "TMtoGS.lean" } ], "Text" ] // Style[ #, "Code" ] &
```

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

Import the Lean proof and inspect the formalization:

```wolfram
env = LeanImportString[ Import[ FileNameJoin[ { leanProjectDir, "Proof", "TMtoGS.lean" } ], "Text" ], "ProjectDir" -> leanProjectDir ]
```

### Formalized constants

```wolfram
Keys[ env ] // Select[ StringContainsQ[ "GS" ] ]
```

### Key definitions and theorems

```wolfram
Grid[
  { #, env[ # ][ "Kind" ], env[ # ][ "TypeForm" ] } & /@ {
    "GS.encodeActive", "GS.decodeActive",
    "GS.encodeBiTM", "GS.decodeBiTM",
    "GS.fromBiTM",
    "GS.decodeActive_encodeActive",
    "GS.decode_encode",
    "GS.step_commutes"
  },
  Frame -> All, Alignment -> Left
]
```

### Core bisimulation statement

The theorem `step_commutes` asserts that one BiTM step corresponds to exactly one GS step under Moore's encoding:

```wolfram
env[ "GS.step_commutes" ][ "TypeForm" ]
```

### Dependency graph

```wolfram
env[ "GS.step_commutes" ][ "ExprGraph" ]
```

### Proof status

Theorems with `sorry` are type-checked but not yet fully proved:

```wolfram
sorryConstants = Select[ Keys[ env ], StringContainsQ[ "GS" ] ];
Grid[
  { #, env[ # ][ "Kind" ] } & /@ sorryConstants,
  Frame -> All, Alignment -> Left
]
```
