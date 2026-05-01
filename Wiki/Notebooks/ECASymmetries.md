# ECA Klein-4 Symmetries (Mirror, Complement, Combined)

The 256 elementary cellular automata are organized by a Klein-4 group of trivial conjugations:

- **Mirror** — `f(a, b, c) = g(c, b, a)` ↔ tape reversal
- **Complement** — `f(a, b, c) = ¬g(¬a, ¬b, ¬c)` ↔ bit complement
- **Composition** — apply both

Each is involutive and they commute, so the orbit of any rule has at most four elements. For Rule 110 the orbit is `{110, 124, 137, 193}`. The two generators give six edges in the universality graph; this notebook proves and visualises all of them as bisimulations with σ = 1, τ = 1.

Reference: Wolfram, [*A New Kind of Science*, Chapter 3](https://www.wolframscience.com/nks/chap-3--the-world-of-simple-programs/) (2002), §3.1, p. 55 (rule equivalences).

## Setup

```wolfram
SetEnvironment[ "PATH" -> Environment[ "PATH" ] <> ":" <> FileNameJoin[ { $HomeDirectory, ".elan", "bin" } ] ];
PacletDirectoryLoad[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "LeanLink", "LeanLink" } ] ];
Get[ "LeanLink`" ];
leanProjectDir = FileNameJoin[ { NotebookDirectory[], "..", "Lean" } ];
```

## 1. Klein-4 Orbit of an ECA Rule

Each ECA rule is a local map `Fin 2 × Fin 2 × Fin 2 → Fin 2`. Wolfram encodes it by listing the outputs for neighbourhoods `111, 110, 101, 100, 011, 010, 001, 000` in that order and reading the resulting 8-bit string as a binary integer. Thus Rule 110 is `01101110`.

The code below accesses the same rule table in the little-endian order used by `BitGet`: bit `4 a + 2 b + c` is the output on neighbourhood `(a, b, c)`, so the bit positions `0, 1, ..., 7` correspond to `000, 001, ..., 111`.

**Mirror** acts by `(a, b, c) → (c, b, a)`, so it swaps bit positions `1 ↔ 4` and `3 ↔ 6`, fixing `0, 2, 5, 7`.

**Complement** acts by `f( a, b, c ) → 1 - f( 1 - a, 1 - b, 1 - c )`, so bit `i` becomes `1 - (bit (7 - i) of original)`.

```wolfram
neighborhoodIndex[ a_, b_, c_ ] := 4 a + 2 b + c

wolframNeighborhoods = Tuples[ { 1, 0 }, 3 ];

wolframRuleTable[ ruleNumber_Integer ] :=
  BitGet[ ruleNumber, neighborhoodIndex @@@ wolframNeighborhoods ]

mirrorRule[ ruleNumber_Integer ] :=
  Sum[ BitGet[ ruleNumber, neighborhoodIndex[ c, b, a ] ] * 2^neighborhoodIndex[ a, b, c ], { a, 0, 1 }, { b, 0, 1 }, { c, 0, 1 } ]

complementRule[ ruleNumber_Integer ] :=
  Sum[ ( 1 - BitGet[ ruleNumber, neighborhoodIndex[ 1 - a, 1 - b, 1 - c ] ] ) * 2^neighborhoodIndex[ a, b, c ], { a, 0, 1 }, { b, 0, 1 }, { c, 0, 1 } ]

orbit[ ruleNumber_Integer ] :=
  DeleteDuplicates @ { ruleNumber, mirrorRule @ ruleNumber, complementRule @ ruleNumber, mirrorRule @ complementRule @ ruleNumber }
```

```wolfram
orbit[ 110 ]
```

Expected: `{110, 124, 137, 193}`.

```wolfram
Row[ { "Rule 110 in Wolfram order: ", wolframRuleTable[ 110 ] } ]
```

Expected: `{0, 1, 1, 0, 1, 1, 1, 0}`, corresponding to `111, 110, 101, 100, 011, 010, 001, 000`.

## 2. Rule Tables Side by Side

```wolfram
littleEndianRuleTable[ ruleNumber_Integer ] :=
  Table[ BitGet[ ruleNumber, i ], { i, 0, 7 } ]
```

We display the rule tables in Wolfram's `111, 110, ..., 000` order. The little-endian `000, 001, ..., 111` order remains useful for bit manipulations.

```wolfram
TableForm[
  Table[ wolframRuleTable[ r ], { r, orbit[ 110 ] } ],
  TableHeadings -> { orbit[ 110 ], Row /@ wolframNeighborhoods }
]
```

```wolfram
TableForm[
  Table[ littleEndianRuleTable[ r ], { r, orbit[ 110 ] } ],
  TableHeadings -> { orbit[ 110 ], Table[ Row @ IntegerDigits[ i, 2, 3 ], { i, 0, 7 } ] }
]
```

## 3. Visual Demonstration

We evolve all four rules from the same random initial tape and apply the corresponding tape transforms. The plots should match (up to permutation/inversion) by the conjugation theorems.

```wolfram
init = RandomInteger[ 1, 80 ];
nSteps = 60;
```

```wolfram
plotEvolution[ rule_Integer, label_String ] :=
  ArrayPlot[ CellularAutomaton[ rule, init, nSteps ],
    Frame -> False, ImageSize -> 250,
    PlotLabel -> Style[ Row @ { "Rule ", rule, " — ", label }, 12 ],
    ColorRules -> { 0 -> Lighter @ Yellow, 1 -> Darker @ Purple } ]
```

```wolfram
Grid @ {
  { plotEvolution[ 110, "original" ], plotEvolution[ 124, "mirror" ] },
  { plotEvolution[ 137, "complement" ], plotEvolution[ 193, "mirror · complement" ] }
}
```

### Verifying the conjugations pointwise

```wolfram
reverseTape[ tape_List ] := Reverse @ tape
complementTape[ tape_List ] := 1 - tape
evolveLast[ rule_Integer, tape_List, k_Integer ] := CellularAutomaton[ rule, tape, k ][[ -1 ]]
```

**Mirror** — `step rule110 (reverse tape) = reverse (step rule124 tape)`:

```wolfram
And @@ Table[
  evolveLast[ 110, reverseTape @ init, k ] === reverseTape @ evolveLast[ 124, init, k ],
  { k, 1, nSteps } ]
```

**Complement** — `step rule110 (complement tape) = complement (step rule137 tape)`:

```wolfram
And @@ Table[
  evolveLast[ 110, complementTape @ init, k ] === complementTape @ evolveLast[ 137, init, k ],
  { k, 1, nSteps } ]
```

**Mirror · Complement** — `step rule110 (reverse · complement tape) = reverse · complement (step rule193 tape)`:

```wolfram
And @@ Table[
  evolveLast[ 110, reverseTape @ complementTape @ init, k ] === reverseTape @ complementTape @ evolveLast[ 193, init, k ],
  { k, 1, nSteps } ]
```

All three should return `True`.

## 4. Lean Verification

The point of this section is not just that Lean accepts the file, but that you can inspect the exact claims being proved.

- The machine definitions live in `Lean/Machines/ElementaryCellularAutomaton/Defs.lean`.
- The conjugation proofs live in `Lean/Proofs/ElementaryCellularAutomatonKleinGroup.lean`.
- The specific edge wrappers live in `Lean/Edges.lean`.

A successful `LeanImportString` means Lean's kernel has accepted every definition and proof in the imported file. The next cells expose the exact statements, so you can check that there are no hidden hypotheses.

### Machine definitions

The ECA rules are defined literally by their Wolfram numbers:

```wolfram
ecaDefsSource = Import[ FileNameJoin[ { leanProjectDir, "Machines", "ElementaryCellularAutomaton", "Defs.lean" } ], "Text" ];

First @ StringCases[
  ecaDefsSource,
  Shortest[
    "def ruleTable" ~~ __ ~~
    "def rule110 : Fin 2 → Fin 2 → Fin 2 → Fin 2 := ruleTable 110\n" ~~
    "def rule124 : Fin 2 → Fin 2 → Fin 2 → Fin 2 := ruleTable 124\n" ~~
    "def rule137 : Fin 2 → Fin 2 → Fin 2 → Fin 2 := ruleTable 137\n" ~~
    "def rule193 : Fin 2 → Fin 2 → Fin 2 → Fin 2 := ruleTable 193"
  ]
]
```

### Klein-group framework (mirror, complement, combined)

```wolfram
envKlein = LeanImportString[ Import[ FileNameJoin[ { leanProjectDir, "Proofs", "ElementaryCellularAutomatonKleinGroup.lean" } ], "Text" ], "ProjectDir" -> leanProjectDir ];
Length[ Keys[ envKlein ] ]
```

The generic, rule-parametric statements:

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.mirrorRuleSimulatesRule" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.ruleSimulatesMirrorRule" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.complementSimulationGeneral" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.mirrorSimulationGenericGeneral" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.mirrorComplementSimulation" ][ "TypeForm" ]
```

The specific Rule 110 orbit identifications are finite equalities of local rules. Each is proved by `decide` over the eight neighbourhoods:

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.mirrorRule_rule110" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.complementRule_rule110" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.mirrorRule_rule137" ][ "TypeForm" ]
```

### Exact edge statements

These are the actual no-hypothesis simulation theorems for the Rule 110 orbit edges:

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.rule110SimulatesRule124" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.rule124SimulatesRule110" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.rule110SimulatesRule137" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.rule137SimulatesRule110" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.rule110SimulatesRule193" ][ "TypeForm" ]
```

```wolfram
envKlein[ "TypeOf", "ElementaryCellularAutomaton.rule193SimulatesRule110" ][ "TypeForm" ]
```

Each of these types is hypothesis-free except for the tape-size side condition `n \[GreaterEqual] 3`, which is mathematically necessary for left and right neighbours to be distinct on the cyclic tape.

**Status.** All six conjugation edges (`110 \[LeftRightArrow] 124`, `110 \[LeftRightArrow] 137`, `110 \[LeftRightArrow] 193`) are fully proved, with axiom closure `[propext, Quot.sound]` and 0 `sorry`. Universality of Rule 110 therefore propagates immediately to Rules 124, 137, and 193.
