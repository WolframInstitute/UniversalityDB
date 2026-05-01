# Cross-Validation: Lean vs. Wolfram

Systematic comparison of Lean definitions against independent Wolfram implementations. If the same machine on the same input produces the same output in both systems, the definitions are likely correct. A disagreement on any input proves a bug.

See [ProofIntegrity](../Concepts/ProofIntegrity.md) for why this matters.

## Setup

```wolfram
(* No LeanLink needed — this notebook uses only built-in Wolfram functions *)
(* as an independent cross-check against the Lean definitions *)
```

## 1. Bi-Infinite Turing Machine: Wolfram's (2,3) UTM

The Lean definition in `Machines/BiInfiniteTuringMachine/Defs.lean` defines `wolfram23` as a 3-state, 3-symbol machine. Lean verifies concrete steps via `native_decide`.

### Lean reference values

From `wolfram23Step1` and `wolfram23Step2` (verified by `native_decide`):

- Initial: state=1, tape=...000**0**000... (head on bold)
- After 1 step: state=2, tape=...001**0**000... (head moved right, wrote 1)
- After 2 steps: state=1, tape=...000**1**200... (head moved left)

### Wolfram cross-check

```wolfram
wolfram23Rules = {
  {1, 0} -> {2, 1, 1},
  {1, 1} -> {1, 2, -1},
  {1, 2} -> {1, 1, -1},
  {2, 0} -> {1, 2, -1},
  {2, 1} -> {2, 2, 1},
  {2, 2} -> {1, 0, 1}
};

tmEvolution = TuringMachine[ wolfram23Rules, { 1, { 0 } }, 5 ];

<|
  "FirstThreeConfigurations" -> tmEvolution[[ 1 ;; 3 ]],
  "StillRunningAfter20Steps" -> MatchQ[
    Last @ TuringMachine[ wolfram23Rules, { 1, { 0 } }, 20 ],
    { { _, _, _ }, _ }
  ],
  "RulePlot" -> RulePlot[ TuringMachine[ wolfram23Rules ], { 1, { 0 } }, 50 ]
|>
```

## 2. Elementary Cellular Automaton: Rule 110

The Lean definition in `Machines/ElementaryCellularAutomaton/Defs.lean` defines `rule110` via `ruleTable 110` which extracts the rule from the binary representation of 110.

### Lean reference

The `mirrorProperty` theorem (verified by `decide`) confirms: `rule110(a,b,c) = rule124(c,b,a)` for all `a, b, c : Fin 2`.

Rule 110 in binary: 01101110
- Neighborhood 111 → 0
- Neighborhood 110 → 1
- Neighborhood 101 → 1
- Neighborhood 100 → 0
- Neighborhood 011 → 1
- Neighborhood 010 → 1
- Neighborhood 001 → 1
- Neighborhood 000 → 0

### Wolfram cross-check

```wolfram
ruleValue[ rule_Integer, triple_List ] := CellularAutomaton[ rule, triple, 1 ][[ -1, 2 ]]

triples = Tuples[ { 0, 1 }, 3 ];
rule110Table = AssociationThread[ triples, ruleValue[ 110, # ] & /@ triples ];

<|
  "Rule110Table" -> rule110Table,
  "MirrorProperty" -> And @@ ( ruleValue[ 110, # ] === ruleValue[ 124, Reverse @ # ] & /@ triples ),
  "EvolutionPlot" -> ArrayPlot[ CellularAutomaton[ 110, { { 1 }, 0 }, 20 ], Mesh -> True ]
|>
```

## 3. Tag System: 2-Tag Example

The Lean definition in `Proofs/TagSystemToCyclicTagSystem.lean` defines `exampleTag2`:
- Alphabet: {0, 1} (k=2)
- Productions: 0 → [1, 0], 1 → [0]
- Deletion number: 2

### Lean reference values

Tag system steps (verified by the simulation theorems):
- `[0, 1, 0]` → delete first 2, append production(0)=[1,0] → `[0, 1, 0]` (fixed point)
- `[1, 0, 1]` → delete first 2, append production(1)=[0] → `[1, 0]`
- `[0, 0, 1, 1]` → delete first 2, append production(0)=[1,0] → `[1, 1, 1, 0]`

### Wolfram cross-check

```wolfram
(* 2-tag system: delete 2, productions 0->[1,0], 1->[0] *)
tagProductions = {{1, 0}, {0}};

(* Manual step function for 2-tag *)
tagStep[word_List] := If[Length[word] < 2, word,
  Join[Drop[word, 2], tagProductions[[word[[1]] + 1]]]
];

(* Or use the ResourceFunction *)
(* ResourceFunction["TagSystem"][{2, {{{1, 0}, {0}}}}, {0, 1, 0}, 1] *)

<|
  "[0,1,0]" -> tagStep[ { 0, 1, 0 } ],
  "[1,0,1]" -> tagStep[ { 1, 0, 1 } ],
  "[0,0,1,1]" -> tagStep[ { 0, 0, 1, 1 } ]
|>
```

## 4. Cyclic Tag System: Cook's Encoding

The Lean definition constructs a CTS from `exampleTag2` with appendants `[[F,T,T,F], [T,F], [], []]` (where T=true, F=false, using 2k=4 appendants).

### Lean reference values

From the simulation verification theorems (verified by `native_decide`):
- Encoded `[0,1,0]` = `[T,F,F,T,T,F]` → after 4 CTS steps → encoded `[0,1,0]` = `[T,F,F,T,T,F]`
- Encoded `[1,0,1]` = `[F,T,T,F,F,T]` → after 4 CTS steps → encoded `[1,0]` = `[F,T,T,F]`
- Encoded `[0,0,1,1]` = `[T,F,T,F,F,T,F,T]` → after 4 CTS steps → encoded `[1,1,1,0]` = `[F,T,F,T,F,T,T,F]`

### Wolfram cross-check

```wolfram
(* One-hot encoding: symbol i in k-alphabet → k-bit word with True at position i+1 *)
symbolEncode[k_, i_] := Table[j == i, {j, 0, k - 1}];
tagWordEncode[k_, word_] := Flatten[symbolEncode[k, #] & /@ word];

(* Build CTS from tag system: 2k appendants *)
(* Production 0 → [1,0]: encode as tagWordEncode[2, {1,0}] = {False,True,True,False} *)
(* Production 1 → [0]: encode as tagWordEncode[2, {0}] = {True,False} *)
(* Then k empty appendants *)
appendants = {
  tagWordEncode[2, {1, 0}],  (* production for symbol 0 *)
  tagWordEncode[2, {0}],      (* production for symbol 1 *)
  {},                           (* empty — padding *)
  {}                            (* empty — padding *)
};

(* CTS step function *)
ctsStep[data_List, phase_Integer, app_List] := Module[{newData, newPhase},
  If[data === {}, {data, phase},
    newPhase = Mod[phase + 1, Length[app]];
    newData = If[First[data],
      Join[Rest[data], app[[phase + 1]]],
      Rest[data]
    ];
    {newData, newPhase}
  ]
];

(* Run 4 CTS steps on encoded [0,1,0] *)
encoded010 = tagWordEncode[2, {0, 1, 0}];
{data, phase} = {encoded010, 0};
Do[{data, phase} = ctsStep[data, phase, appendants], {4}];
match010 = data === tagWordEncode[2, {0, 1, 0}];

(* Run 4 CTS steps on encoded [1,0,1] *)
encoded101 = tagWordEncode[2, {1, 0, 1}];
{data, phase} = {encoded101, 0};
Do[{data, phase} = ctsStep[data, phase, appendants], {4}];
result101 = data;
match101 = data === tagWordEncode[2, {1, 0}];

(* Run 4 CTS steps on encoded [0,0,1,1] *)
encoded0011 = tagWordEncode[2, {0, 0, 1, 1}];
{data, phase} = {encoded0011, 0};
Do[{data, phase} = ctsStep[data, phase, appendants], {4}];
<|
  "symbolEncode(2,0)" -> symbolEncode[ 2, 0 ],
  "symbolEncode(2,1)" -> symbolEncode[ 2, 1 ],
  "tagWordEncode(2,{0,1})" -> tagWordEncode[ 2, { 0, 1 } ],
  "Appendants" -> appendants,
  "Match010" -> match010,
  "Result101" -> result101,
  "Match101" -> match101,
  "Result0011" -> data,
  "Match0011" -> ( data === tagWordEncode[ 2, { 1, 1, 1, 0 } ] )
|>
```

## 5. Generalized Shift: TM ↔ GS Roundtrip

The Lean definition in `Proofs/TuringMachineToGeneralizedShift.lean` constructs a GS from a (2,2) TM (`exampleTuringMachine`) and verifies 30 steps of commutation.

### Lean reference

The `exampleTuringMachine` has 2 states, 2 symbols:
- (1,0) → write=1, state=2, R
- (1,1) → write=1, state=1, L
- (2,0) → write=1, state=1, L
- (2,1) → write=0, state=2, R

The encoding merges state into the tape alphabet (extended alphabet size = states * symbols + symbols = 2*2+2 = 6). Window width = 3.

`verifySteps` confirms that for 30 steps: encoding a TM config to GS, stepping the GS, and decoding back yields the same result as stepping the TM directly.

### Wolfram cross-check

```wolfram
tmRule = {
  {1, 0} -> {2, 1, 1},
  {1, 1} -> {1, 1, -1},
  {2, 0} -> {1, 1, -1},
  {2, 1} -> {2, 0, 1}
};

init = { 1, { 0 } };
steps = TuringMachine[ tmRule, init, 5 ];

<|
  "FirstSixTMConfigurations" -> steps,
  "Comment" -> "The GeneralizedShift ResourceFunction can be used separately to compare with the Lean encoding on this same TM."
|>
```

## Summary

If all cross-checks produce matching results, the Lean definitions agree with Wolfram's independent implementations. Any disagreement identifies a definition bug that must be fixed before the formal proofs built on that definition can be trusted.
