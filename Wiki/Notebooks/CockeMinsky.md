# Cocke-Minsky Universality Chain

The Cocke-Minsky theorem establishes that any Turing machine can be simulated by a 2-tag system. Combined with Cook's encoding (Tag -> CTS) and Smith's proof (CTS -> (2,3) TM), this gives the universality chain:

**Any TM -> 2-Tag (Cocke-Minsky 1964) -> CTS (Cook 2004) -> (2,3) TM (Smith 2007)**

References:
- Cocke, J. (1964). Abstract 611-52, Notices AMS 11(3).
- Minsky, M. (1967). *Computation: Finite and Infinite Machines*, Ch. 14.
- Cook, M. (2004). *Universality in Elementary Cellular Automata*, Complex Systems 15(1).
- Smith, A. (2007). *Universality of Wolfram's 2,3 Turing Machine*.

## Setup

```wolfram
SetEnvironment[ "PATH" -> Environment[ "PATH" ] <> ":" <> FileNameJoin[ { $HomeDirectory, ".elan", "bin" } ] ]
PacletDirectoryLoad[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "LeanLink", "LeanLink" } ] ];
Get[ "LeanLink`" ]
leanProjectDir = FileNameJoin[ { NotebookDirectory[], "..", "Lean" } ]
tmProofsDir = FileNameJoin[ { NotebookDirectory[], "..", "Resources", "TuringMachine", "Proofs" } ]
```

```wolfram
Get[ FileNameJoin[ { NotebookDirectory[], "..", "Wolfram", "Encoding", "TM_Tag.wl" } ] ]
Get[ FileNameJoin[ { NotebookDirectory[], "..", "Wolfram", "Encoding", "Tag_CTS.wl" } ] ]
```

## 1. Machine Definitions

### Turing Machine (BiTM)

```wolfram
Import[ FileNameJoin[ { tmProofsDir, "BiTM", "Basic.lean" } ], "Text" ]
```

### 2-Tag System

A 2-tag system reads the first symbol, deletes the first 2 symbols, appends the production for the read symbol. Halts when the word has fewer than 2 symbols.

```wolfram
Import[ FileNameJoin[ { tmProofsDir, "TagSystem", "Basic.lean" } ], "Text" ]
```

### Cyclic Tag System

Binary alphabet. Each step: if the first bit is true, append the current appendant; delete the first bit; advance to the next appendant (cycling). Halts when the data word is empty.

```wolfram
Import[ FileNameJoin[ { tmProofsDir, "TagSystem", "TagToCTS.lean" } ], "Text" ]
```

## 2. Step 1: TM -> 2-Tag (Cocke-Minsky 1964)

The encoding maps a TM config to a tag word. Alphabet size = s*k + k + 1 where s = states, k = symbols. Symbols: A(q,a) for state-symbol pairs, B(a) for tape cells, C for separator. Format: A(q, head) . B(right) . C . B(left).

```wolfram
Import[ FileNameJoin[ { tmProofsDir, "BiTM", "CockeMinsky.lean" } ], "Text" ]
```

### Validation

```wolfram
tmRules = { {1, 0} -> {2, 1, 1}, {1, 1} -> {1, 1, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 0, 1} };
numStates = 2; numColors = 2;
tagProds = CockeMinskyProductions[ tmRules, numStates, numColors ];
initTape = ConstantArray[ 0, 11 ]; initHead = 6; initState = 1;
tagWord = CockeMinskyEncode[ { initTape, initHead, initState }, numStates, numColors ];
Column[ { Row[ { "Tag alphabet size: ", CockeMinskyTagSize[ numStates, numColors ] } ], Row[ { "Initial tag word: ", tagWord } ] } ]
```

## 3. Step 2: Tag -> CTS (Cook 2004)

One-hot binary encoding: symbol i in alphabet k becomes a binary word of length k with true at position i. The CTS has 2k appendants: first k encode productions, next k are empty (consume the second deleted symbol). One tag step = 2k CTS steps.

### Validation

```wolfram
k = CockeMinskyTagSize[ numStates, numColors ];
appendants = TagToCTSAppendants[ tagProds, k ];
ctsInit = TagToCTSEncode[ tagWord, k ];
Column[ { Row[ { "CTS appendants: ", Length[ appendants ] } ], Row[ { "CTS data length: ", Length[ ctsInit[[ 1 ]] ] } ] } ]
```

## 4. Lean Verification

### Cocke-Minsky (TM -> Tag)

```wolfram
envCM = LeanImportString[ Import[ FileNameJoin[ { tmProofsDir, "BiTM", "CockeMinsky.lean" } ], "Text" ], "ProjectDir" -> FileNameJoin[ { tmProofsDir, ".." } ] ]
```

```wolfram
envCM[ "Constants" ] // Select[ StringContainsQ[ #, "cockeMinsky" | "wolfram23" ] & ]
```

Key theorems:
- `cockeMinsky_halting_forward`: TM halts -> Tag halts (given step sim hypothesis)
- `tm_to_cts`: TM halts -> CTS halts (Cocke-Minsky + Cook composed)
- `wolfram23_universal`: (2,3) TM is universal (given Cocke-Minsky + Smith hypotheses)

```wolfram
envCM[ "TypeOf", "BiTM.wolfram23_universal" ][ "TypeForm" ]
```

### Tag -> CTS (Cook, fully proved)

```wolfram
envCook = LeanImportString[ Import[ FileNameJoin[ { tmProofsDir, "TagSystem", "TagToCTS.lean" } ], "Text" ], "ProjectDir" -> FileNameJoin[ { tmProofsDir, ".." } ] ]
```

```wolfram
envCook[ "Constants" ] // Select[ StringContainsQ[ #, "tagToCTS" ] & ]
```

Key theorem: `tagToCTS_simulation` — one tag step corresponds to exactly 2k CTS steps. Fully proved, 0 sorry.

```wolfram
envCook[ "TypeOf", "TagSystem.tagToCTS_simulation" ][ "TypeForm" ]
```

Status: Tag -> CTS fully proved. TM -> Tag step simulation and CTS -> (2,3) TM simulation are stated as explicit hypotheses. The composition theorem `wolfram23_universal` is fully proved given these hypotheses.
