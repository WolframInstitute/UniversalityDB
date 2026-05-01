# TM ↔ Generalized Shift (Moore 1991)

Moore's 1991 paper proves that **Turing machines and generalized shifts are conjugate**: any TM can be simulated by a GS and vice versa, with explicit overhead bounds. Both directions are now formalized in Lean (0 sorry, axiom closure `[propext, Quot.sound, Classical.choice]`).

| Direction | Theorem | Overhead | Lean | Status |
|---|---|---|---|---|
| TM → GS | Theorem 7 | σ=1, τ=1 (window width 3) | `TMtoGS.tmToGSSimulation` | 0 sorry |
| GS → TM | Theorem 8 | σ=1, τ=2(w−1)+m | `GeneralizedShiftToTuringMachine.gsToTMSimulationEncoding` | 0 sorry |

Reference: C. Moore, *Generalized shifts: unpredictability and undecidability in dynamical systems*, Nonlinearity 4 (1991) 199–230.

## Setup

```wolfram
SetEnvironment[ "PATH" -> Environment[ "PATH" ] <> ":" <> FileNameJoin[ { $HomeDirectory, ".elan", "bin" } ] ];
PacletDirectoryLoad[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "LeanLink", "LeanLink" } ] ];
Get[ "LeanLink`" ];
leanProjectDir = FileNameJoin[ { NotebookDirectory[], "..", "Lean" } ];
```

```wolfram
Get[ FileNameJoin[ { NotebookDirectory[], "..", "Wolfram", "Encoding", "TM_GS.wl" } ] ];
```

## 1. Machine Definitions

**Bi-infinite Turing Machine.** State in `{0, 1, ..., s}` (state 0 = halted), symbols in `{0, 1, ..., k-1}`, tape extends to ±∞ (default cell = 0). A configuration is `<| "state", "left", "head", "right" |>` where `left` and `right` are lists of cells (nearest-first). Source: `Resources/TuringMachine/Proofs/BiTM/Basic.lean`.

**Generalized Shift.** A stateless dynamical system on a bi-infinite tape with a sliding window of fixed width `w`. Each step rewrites the window via a transition function and shifts the window by a rule-determined amount. A configuration is `<| "left", "cells", "right" |>` where `cells` is the window contents. Source: `Lean/Machines/GeneralizedShift/Defs.lean`.

The two directions in the title are *both* simulation encodings — `step_B(b) = decode (step_A^n (encode b))`.

## 2. TM → GS  (Moore Theorem 7)

### Encoding

Moore's **state-into-tape** encoding: extend the alphabet to size `s*k + k`. Cells `0..k-1` are *passive* (just a tape symbol); cells in `[k, s*k+k)` are *active* and encode `(state, color)` as `k + (state - 1)*k + color`. The GS window has width 3: `[leftNeighbor, activeCell, rightNeighbor]`.

Source: [Lean/Proofs/TuringMachineToGeneralizedShift.lean](../../Lean/Proofs/TuringMachineToGeneralizedShift.lean) — `encodeActive`, `encodeBiTM`, `fromBiTM`.

### Define a small TM

A 2-state, 2-symbol TM (busy-beaver-style):

```wolfram
tm = <|
  "numStates" -> 2,
  "numSymbols" -> 2,
  "transition" -> Function[ qc,
    Switch[ qc,
      {1, 0}, <| "nextState" -> 2, "write" -> 1, "direction" -> "R" |>,
      {1, 1}, <| "nextState" -> 1, "write" -> 1, "direction" -> "L" |>,
      {2, 0}, <| "nextState" -> 1, "write" -> 1, "direction" -> "L" |>,
      {2, 1}, <| "nextState" -> 2, "write" -> 0, "direction" -> "R" |>
    ]
  ]
|>
```

Initial config — head on a blank tape, state 1:

```wolfram
tmStart = <| "state" -> 1, "left" -> {}, "head" -> 0, "right" -> {} |>
```

### Build the simulating GS

`TMtoGSMachine` constructs the GS from the TM following Moore's encoding:

```wolfram
gs = TMGSEncoding`TMtoGSMachine[ tm ];
{ "alphabet" -> gs[ "alphabet" ], "windowWidth" -> gs[ "width" ] }
```

Encode the initial TM config as a GS config:

```wolfram
gsStart = TMGSEncoding`TMtoGSEncodeConfig[ tmStart, tm ]
```

The middle cell `4 = TMtoGSEncodeActive[ 1, 0, 2 ]` encodes `(state=1, color=0)`.

### Run both, side-by-side

```wolfram
nSteps = 12;
tmTraj = NestList[ TMGSEncoding`BiTMStep[ #, tm ] &, tmStart, nSteps ];
gsTraj = NestList[ TMGSEncoding`GSStep[ #, gs ] &, gsStart, nSteps ];
```

### Bisimulation check

Encode each TM step then strip trailing zeros (the GS introduces a `[0]` phantom on initially empty tapes; the bisimulation holds modulo trailing-zero canonicalization, which is exactly what `BiInfiniteTuringMachine.step_stripConfig_bisim` proves on the Lean side):

```wolfram
encodedTraj = TMGSEncoding`TMtoGSEncodeConfig[ #, tm ] & /@ tmTraj;
match = ( TMGSEncoding`StripGSConfig /@ encodedTraj ) ===
         ( TMGSEncoding`StripGSConfig /@ gsTraj );
{ "All steps match modulo strip:", match }
```

### Visualize the GS evolution

```wolfram
ArrayPlot[
  PadRight[ Join[ Reverse @ #[ "left" ], #[ "cells" ], #[ "right" ] ], 15, 0 ] & /@ gsTraj,
  Frame -> False, Mesh -> All, MeshStyle -> GrayLevel[ 0.85 ],
  ColorRules -> { 0 -> White, 1 -> Black, _Integer?Positive -> RGBColor[ 1, 0.5, 0.3 ] },
  ImageSize -> 500, PlotLabel -> "GS evolution (orange = active cell encoding TM state)"
]
```

## 3. GS → TM  (Moore Theorem 8)

### Encoding

A GS configuration `{left, cells, right}` with `cells.length = w` is encoded as the TM configuration `{state := 1, left, head := cells[1], right := Rest[cells] ~Join~ right}` — the head sits on the leftmost window cell and the rest of the window is prepended to the right tape.

Each GS step is simulated by `2(w−1) + m` TM steps in three phases:

| Phase | Steps | What the TM does |
|---|---|---|
| **Read** | `w − 1` | scan right, accumulate window contents in state |
| **Write** | `w − 1` | write replacement symbols right-to-left |
| **Shift** | `m` | move head to match GS shift |

The TM uses a Nat-encoded state representing the inductive type `TMPhase = halt | start | read pos partialCode | write pos windowCode | shift remaining goLeft`.

Source: [Lean/Proofs/GeneralizedShiftToTuringMachine.lean](../../Lean/Proofs/GeneralizedShiftToTuringMachine.lean) — `TMPhase`, `phaseTransition`, `toBiTM`, `encodeConfig`, `decodeConfigPadded`.

### Define a small GS

A 3-cell window over a binary alphabet, with a non-trivial transition that exercises both shift directions:

```wolfram
gsParams = <|
  "alphabet" -> 2,
  "width" -> 3,
  "maxShift" -> 1,
  "active" -> Function[ window, window =!= {0, 0, 0} ],
  "transition" -> Function[ window,
    <| "replacement" -> RotateLeft @ window,
       "magnitude" -> 1,
       "shiftLeft" -> EvenQ @ Total @ window |>
  ]
|>
```

```wolfram
gsStartCfg = <| "left" -> {}, "cells" -> {1, 0, 1}, "right" -> {1, 1, 0} |>
```

### Build the simulating TM

`GStoTMMachine` constructs the BiTM from the GS parameters following Moore's three-phase encoding:

```wolfram
simTM = TMGSEncoding`GStoTMMachine[ gsParams ];
overhead = TMGSEncoding`GStoTMTemporalOverhead[ gsParams ];
{ "TM states" -> simTM[ "numStates" ],
  "alphabet" -> simTM[ "numSymbols" ],
  "BiTM steps per GS step" -> overhead }
```

Encode the GS config in the TM's `[c]`-view:

```wolfram
tmStartCfg = TMGSEncoding`GStoTMEncodeConfig[ gsStartCfg ]
```

### Run both, side-by-side

```wolfram
nGSSteps = 6;
gsTraj2 = NestList[ TMGSEncoding`GSStep[ #, gsParams ] &, gsStartCfg, nGSSteps ];
tmTraj2 = NestList[ TMGSEncoding`BiTMStep[ #, simTM ] &, tmStartCfg, nGSSteps * overhead ];
```

Sample the TM every `overhead` steps and decode (with `decodeConfigPadded`, which pads cells with 0 when the right tape underflows):

```wolfram
sampled = tmTraj2[[ 1 ;; ;; overhead ]];
decoded = TMGSEncoding`GStoTMDecodeConfigPadded[ #, gsParams[ "width" ] ] & /@ sampled;
```

### Bisimulation check

```wolfram
match2 = ( TMGSEncoding`StripGSConfig /@ decoded ) ===
          ( TMGSEncoding`StripGSConfig /@ gsTraj2 );
{ "All steps match modulo strip:", match2 }
```

### Visualize the BiTM trace

The TM cycles through three phases per GS step: read (w−1 steps right) → write (w−1 steps left) → shift (m steps). Color by phase (read = blue, write = green, shift = red, start = yellow):

```wolfram
phaseTag[ tmCfg_, params_ ] :=
  Module[ { wsBase = 2 + params[ "width" ] * params[ "alphabet" ]^params[ "width" ],
            shBase },
    shBase = wsBase + params[ "width" ] * params[ "alphabet" ]^params[ "width" ];
    Which[
      tmCfg[ "state" ] == 0, "halt",
      tmCfg[ "state" ] == 1, "start",
      2 <= tmCfg[ "state" ] < wsBase, "read",
      wsBase <= tmCfg[ "state" ] < shBase, "write",
      True, "shift"
    ]
  ];

phases = phaseTag[ #, gsParams ] & /@ tmTraj2;
phaseColor = <| "halt" -> Gray, "start" -> Yellow,
                "read" -> RGBColor[ 0.3, 0.5, 1 ],
                "write" -> RGBColor[ 0.3, 0.8, 0.3 ],
                "shift" -> RGBColor[ 1, 0.4, 0.4 ] |>;

Grid[
  { Range[ 0, Length @ tmTraj2 - 1 ],
    Style[ #, Bold, phaseColor[ # ] ] & /@ phases }
  , Frame -> All, FrameStyle -> GrayLevel[ 0.8 ]
]
```

## 4. Lean Verification

> A successful `LeanImportString` (no error returned) means Lean's kernel has accepted every definition and proof in the file. If this cell fails, no theorem below can be trusted.

```wolfram
envTM = LeanImportString[ Import[ FileNameJoin[ { leanProjectDir, "Proofs", "TMtoGS.lean" } ], "Text" ], "ProjectDir" -> leanProjectDir ];
envGS = LeanImportString[ Import[ FileNameJoin[ { leanProjectDir, "Proofs", "GeneralizedShiftToTuringMachine.lean" } ], "Text" ], "ProjectDir" -> leanProjectDir ];
{ "TMtoGS keys" -> Length @ Keys @ envTM, "GStoTM keys" -> Length @ Keys @ envGS }
```

### TM → GS main theorem

`TMtoGS.tmToGSSimulation` returns a `ComputationalMachine.SimulationEncoding` whose `commutes` field is the strict conjugation `step_BiTM(b) = decode (step_GS^n (encode b))`. The B-side is the *normalized* BiTM (`stepNormalized` post-strips trailing zeros), so the conjugation is strict — no "modulo normalize" qualifier.

> Read the type. Any extra hypothesis weakens the claim — the only hypotheses are the four well-formedness conditions (`_hk`, `_hHeadAll`, `_hWriteBound`, `_hStateBound`).

```wolfram
envTM[ "TMtoGS.tmToGSSimulation" ][ "TypeForm" ]
```

### GS → TM main theorem

`GeneralizedShiftToTuringMachine.gsToTMSimulationEncoding` returns a `SimulationEncoding` whose `commutes` field is the conjugation `step_GS(b) = decodePadded (step_BiTM^{2(w−1)+m} (encode b))`. Decode is `decodeConfigPadded` — it pads cells with `0` when the right tape underflows, absorbing the `[0]`-phantom that arises from short-tape `shiftRightOne`.

> Verify the only hypotheses are seven well-formedness conditions (`hAlpha`, `hWidth`, `hLen`, `hShift`, `hRepl`, `hCellBoundAll`, `hHalt`).

```wolfram
envGS[ "GeneralizedShiftToTuringMachine.gsToTMSimulationEncoding" ][ "TypeForm" ]
```

### The chain (`fullSim_general_cView`)

The substantial part of GS → TM is the *chain* — discharging `2(w−1) + m` BiTM steps from the encoded GS config to the encoded shifted [c]-view:

```wolfram
envGS[ "GeneralizedShiftToTuringMachine.fullSim_general_cView" ][ "TypeForm" ]
```

This theorem has **empty axiom closure** (`[]`) — no propext, no choice, no sorry. The bridge from the chain output to the multi-cell view is then provided by `decodePadded_shiftByRight` and `decodePadded_shiftByLeft`.
