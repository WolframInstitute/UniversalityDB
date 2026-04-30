# ECA Klein-4 Symmetries (Mirror, Complement, Combined)

The 256 elementary cellular automata are organized by a Klein-4 group of trivial conjugations:

- **Mirror** — `f(a, b, c) = g(c, b, a)` ↔ tape reversal
- **Complement** — `f(a, b, c) = ¬g(¬a, ¬b, ¬c)` ↔ bit complement
- **Composition** — apply both

Each is involutive and they commute, so the orbit of any rule has at most four elements. For Rule 110 the orbit is `{110, 124, 137, 193}`. The two generators give six edges in the universality graph; this notebook proves and visualises all of them as bisimulations with σ = 1, τ = 1.

Reference: Wolfram, *A New Kind of Science* (2002), §3.1, p. 55 (rule equivalences).

## Setup

```wolfram
SetEnvironment[ "PATH" -> Environment[ "PATH" ] <> ":" <> FileNameJoin[ { $HomeDirectory, ".elan", "bin" } ] ];
PacletDirectoryLoad[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "LeanLink", "LeanLink" } ] ];
Get[ "LeanLink`" ];
leanProjectDir = FileNameJoin[ { NotebookDirectory[], "..", "Lean" } ];
```

## 1. Klein-4 Orbit of an ECA Rule

Each ECA rule is a function `Fin 2 \[Times] Fin 2 \[Times] Fin 2 \[RightArrow] Fin 2`, encoded by an 8-bit Wolfram rule number. The bit at position `4 a + 2 b + c` records the output for neighbourhood `(a, b, c)`.

**Mirror** swaps the position bits at indices `abc` and `cba` (positions 1↔4, 3↔6, fixed at 0, 2, 5, 7).

**Complement** flips all bits and reverses index order: bit `i` of the new rule is `1 - (bit (7 - i) of original)`.

```wolfram
neighborhoodIndex[ a_, b_, c_ ] := 4 a + 2 b + c

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

## 2. Rule Tables Side by Side

```wolfram
ruleTable[ ruleNumber_Integer ] :=
  Table[ BitGet[ ruleNumber, i ], { i, 0, 7 } ]
```

Each row gives the rule's outputs for neighbourhoods `000, 001, 010, ..., 111` (in that order).

```wolfram
TableForm[
  Table[ ruleTable[ r ], { r, orbit[ 110 ] } ],
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
  { plotEvolution[ 137, "complement" ], plotEvolution[ 193, "mirror \[CenterDot] complement" ] }
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

**Mirror \[CenterDot] Complement** — `step rule110 (reverse \[CenterDot] complement tape) = reverse \[CenterDot] complement (step rule193 tape)`:

```wolfram
And @@ Table[
  evolveLast[ 110, reverseTape @ complementTape @ init, k ] === reverseTape @ complementTape @ evolveLast[ 193, init, k ],
  { k, 1, nSteps } ]
```

All three should return `True`.

## 4. Lean Verification

> A successful `LeanImportString` means Lean's kernel has accepted every definition and proof in the file. The conjugation file is rule-parametric: the specific edges `rule110 \[LeftRightArrow] rule137` and `rule110 \[LeftRightArrow] rule193` follow from generic theorems plus `decide`-checkable rule identifications.

### Mirror (Rule 110 \[LeftRightArrow] Rule 124)

```wolfram
envMirror = LeanImportString[ Import[ FileNameJoin[ { leanProjectDir, "Proofs", "ElementaryCellularAutomatonMirror.lean" } ], "Text" ], "ProjectDir" -> leanProjectDir ];
Length[ Keys[ envMirror ] ]
```

```wolfram
envMirror[ "TypeOf", "ElementaryCellularAutomaton.rule110SimulatesRule124" ][ "TypeForm" ]
```

### Conjugation framework (Klein-4)

```wolfram
envConj = LeanImportString[ Import[ FileNameJoin[ { leanProjectDir, "Proofs", "ElementaryCellularAutomatonConjugation.lean" } ], "Text" ], "ProjectDir" -> leanProjectDir ];
Length[ Keys[ envConj ] ]
```

The generic, rule-parametric theorems:

```wolfram
envConj[ "TypeOf", "ElementaryCellularAutomaton.complementSimulationGeneral" ][ "TypeForm" ]
```

```wolfram
envConj[ "TypeOf", "ElementaryCellularAutomaton.mirrorSimulationGenericGeneral" ][ "TypeForm" ]
```

The specific Rule 110 orbit identifications (each is a `decide` over 8 neighbourhoods):

```wolfram
envConj[ "TypeOf", "ElementaryCellularAutomaton.mirrorRule_rule110" ][ "TypeForm" ]
```

```wolfram
envConj[ "TypeOf", "ElementaryCellularAutomaton.complementRule_rule110" ][ "TypeForm" ]
```

```wolfram
envConj[ "TypeOf", "ElementaryCellularAutomaton.mirrorRule_rule137" ][ "TypeForm" ]
```

The two new edges:

```wolfram
envConj[ "TypeOf", "ElementaryCellularAutomaton.rule110SimulatesRule137" ][ "TypeForm" ]
```

```wolfram
envConj[ "TypeOf", "ElementaryCellularAutomaton.rule110SimulatesRule193" ][ "TypeForm" ]
```

**Status.** All six conjugation edges (`110 \[LeftRightArrow] 124`, `110 \[LeftRightArrow] 137`, `110 \[LeftRightArrow] 193`) fully proved, axiom closure `[propext, Quot.sound]`, 0 sorry. Universality of Rule 110 (Cook 2004) therefore propagates to Rules 124, 137, 193.
