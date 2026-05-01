(* ::Package:: *)

(*  TM_GS.wl  ─  Moore 1991 encodings between Turing machines (bi-infinite tape)
    and generalized shifts, in both directions.

    Conventions (matching Lean/Proofs/{TuringMachineToGeneralizedShift,
    GeneralizedShiftToTuringMachine, TMtoGS}.lean):

      Bi-infinite TM config (BiTMConfig):
        <|
          "state"  -> Integer (0 = halt; states ≥ 1 are running),
          "left"   -> List of cells (nearest first; tape extends to -∞ as 0s),
          "head"   -> Integer (current cell, 0 ≤ head < numSymbols),
          "right"  -> List of cells (nearest first; tape extends to +∞ as 0s)
        |>

      BiTM machine (BiTM):
        <|
          "numStates"  -> s (states 1..s; 0 reserved for halt),
          "numSymbols" -> k (symbols 0..k-1),
          "transition" -> Function: {q, c} \[Function]
            <| "nextState" -> q' (0 = halt), "write" -> w, "direction" -> "L"|"R" |>
        |>

      GS config:
        <| "left" -> {...}, "cells" -> {...}, "right" -> {...} |>

      GS machine:
        <|
          "alphabet"   -> Integer (alphabet size),
          "width"      -> Integer (window width w),
          "transition" -> Function: window \[Function]
            <| "replacement" -> List, "magnitude" -> Integer, "shiftLeft" -> True|False |>,
          "active"     -> Function: window \[Function] True|False
        |>
*)

BeginPackage[ "TMGSEncoding`" ]

(* ─── Stepping primitives ──────────────────────────────────────────────── *)

BiTMStep::usage     = "BiTMStep[ tmConfig, machine ] takes one bi-infinite TM step.  Returns a new config or Missing[\"halted\"]."

GSStep::usage       = "GSStep[ gsConfig, gsMachine ] takes one generalized-shift step.  Returns a new config or Missing[\"halted\"]."

(* ─── Canonicalization (strip trailing zeros from both tapes) ────────── *)

StripTrailingZeros::usage = "StripTrailingZeros[ list ] drops trailing zeros from `list`."

StripBiTMConfig::usage    = "StripBiTMConfig[ tmConfig ] strips trailing zeros from both tapes."

StripGSConfig::usage      = "StripGSConfig[ gsConfig ] strips trailing zeros from both tapes (cells are left untouched)."

(* ─── TM \[RightArrow] GS  (Moore Theorem 7) ─────────────────────────── *)

TMtoGSEncodeActive::usage = "TMtoGSEncodeActive[ state, color, k ] returns the active-cell value k + (state - 1)*k + color."

TMtoGSDecodeActive::usage = "TMtoGSDecodeActive[ value, k ] returns {state, color}, the inverse of TMtoGSEncodeActive."

TMtoGSEncodeConfig::usage = "TMtoGSEncodeConfig[ tmConfig, machine ] encodes a BiTM config as a 3-cell GS config (state-into-tape encoding)."

TMtoGSDecodeConfig::usage = "TMtoGSDecodeConfig[ gsConfig, machine ] inverts TMtoGSEncodeConfig (returns Missing[] if the window is malformed)."

TMtoGSMachine::usage = "TMtoGSMachine[ machine ] returns the generalized-shift machine that simulates `machine` (windowWidth = 3, alphabet = s*k + k)."

(* ─── GS \[RightArrow] TM  (Moore Theorem 8) ─────────────────────────── *)

GStoTMEncodeConfig::usage = "GStoTMEncodeConfig[ gsConfig ] encodes a GS config as a BiTM config in the [c]-view: state = 1, head = cells[1], right = Rest[cells] ~Join~ right."

GStoTMDecodeConfigPadded::usage = "GStoTMDecodeConfigPadded[ tmConfig, w ] decodes a state-1 BiTM config into a w-cell GS config, padding cells with 0 if the right tape is shorter than w-1."

GStoTMMachine::usage = "GStoTMMachine[ gsParams ] returns the bi-infinite TM that simulates `gsParams`.  Each GS step lifts to 2(w-1) + m TM steps (m = shift magnitude of the active rule)."

GStoTMTemporalOverhead::usage = "GStoTMTemporalOverhead[ gsParams ] returns 2(w-1) + maxShift, the per-step BiTM step budget."

Begin[ "`Private`" ]

(* ──────────────────────────────────────────────────────────────────────────
   Stepping primitives
   ────────────────────────────────────────────────────────────────────────── *)

readHead[ tape_List ] :=
  If[ tape === {}, { 0, {} }, { First @ tape, Rest @ tape } ]

StripTrailingZeros[ list_List ] :=
  If[ list === {} || Last @ list =!= 0, list,
      StripTrailingZeros @ Most @ list ]

StripBiTMConfig[ tmConfig_Association ] :=
  <| "state" -> tmConfig[ "state" ],
     "left"  -> StripTrailingZeros @ tmConfig[ "left" ],
     "head"  -> tmConfig[ "head" ],
     "right" -> StripTrailingZeros @ tmConfig[ "right" ] |>

StripGSConfig[ gsConfig_Association ] :=
  <| "left"  -> StripTrailingZeros @ gsConfig[ "left" ],
     "cells" -> gsConfig[ "cells" ],
     "right" -> StripTrailingZeros @ gsConfig[ "right" ] |>

BiTMStep[ tmConfig_Association, machine_Association ] :=
  Module[ { state = tmConfig[ "state" ], head = tmConfig[ "head" ],
            left = tmConfig[ "left" ], right = tmConfig[ "right" ],
            rule, ns, w, d, newHead, newRest },
    If[ state == 0, Return @ Missing[ "halted" ] ];
    rule = machine[ "transition" ][ { state, head } ];
    ns   = rule[ "nextState" ];
    w    = rule[ "write" ];
    d    = rule[ "direction" ];
    Switch[ d,
      "L",
        { newHead, newRest } = readHead @ left;
        <| "state" -> ns, "left" -> newRest, "head" -> newHead,
           "right" -> Prepend[ right, w ] |>,
      "R",
        { newHead, newRest } = readHead @ right;
        <| "state" -> ns, "left" -> Prepend[ left, w ], "head" -> newHead,
           "right" -> newRest |>
    ]
  ]

shiftRightOne[ gsConfig_Association ] :=
  Module[ { left = gsConfig[ "left" ], cells = gsConfig[ "cells" ],
            right = gsConfig[ "right" ], newLeft, tail, r, rs },
    newLeft = If[ cells === {}, left, Prepend[ left, First @ cells ] ];
    tail = If[ cells === {}, {}, Rest @ cells ];
    If[ right === {},
      <| "left" -> newLeft, "cells" -> Append[ tail, 0 ], "right" -> {} |>,
      r = First @ right; rs = Rest @ right;
      <| "left" -> newLeft, "cells" -> Append[ tail, r ], "right" -> rs |>
    ]
  ]

shiftLeftOne[ gsConfig_Association ] :=
  Module[ { left = gsConfig[ "left" ], cells = gsConfig[ "cells" ],
            right = gsConfig[ "right" ], lastCell, init, l, ls },
    lastCell = If[ cells === {}, 0, Last @ cells ];
    init = If[ cells === {}, {}, Most @ cells ];
    If[ left === {},
      <| "left" -> {}, "cells" -> Prepend[ init, 0 ], "right" -> Prepend[ right, lastCell ] |>,
      l = First @ left; ls = Rest @ left;
      <| "left" -> ls, "cells" -> Prepend[ init, l ], "right" -> Prepend[ right, lastCell ] |>
    ]
  ]

shiftBy[ gsConfig_Association, magnitude_Integer, goLeft : (True | False) ] :=
  Nest[ If[ goLeft, shiftLeftOne, shiftRightOne ], gsConfig, magnitude ]

GSStep[ gsConfig_Association, gsMachine_Association ] :=
  Module[ { cells = gsConfig[ "cells" ], rule, replaced },
    If[ ! gsMachine[ "active" ][ cells ], Return @ Missing[ "halted" ] ];
    rule = gsMachine[ "transition" ][ cells ];
    replaced = <| "left" -> gsConfig[ "left" ],
                  "cells" -> rule[ "replacement" ],
                  "right" -> gsConfig[ "right" ] |>;
    shiftBy[ replaced, rule[ "magnitude" ], rule[ "shiftLeft" ] ]
  ]

(* ──────────────────────────────────────────────────────────────────────────
   TM \[RightArrow] GS  (Moore Theorem 7)
   ────────────────────────────────────────────────────────────────────────── *)

TMtoGSEncodeActive[ state_Integer, color_Integer, k_Integer ] :=
  k + ( state - 1 ) * k + color

TMtoGSDecodeActive[ value_Integer, k_Integer ] :=
  { Quotient[ value - k, k ] + 1, Mod[ value - k, k ] }

TMtoGSEncodeConfig[ tmConfig_Association, machine_Association ] :=
  Module[ { state = tmConfig[ "state" ], head = tmConfig[ "head" ],
            left = tmConfig[ "left" ], right = tmConfig[ "right" ],
            k = machine[ "numSymbols" ], leftCell, rightCell, activeCell },
    leftCell  = If[ left  === {}, 0, First @ left ];
    rightCell = If[ right === {}, 0, First @ right ];
    activeCell = If[ state == 0, head, TMtoGSEncodeActive[ state, head, k ] ];
    <| "left"  -> If[ left === {}, {}, Rest @ left ],
       "cells" -> { leftCell, activeCell, rightCell },
       "right" -> If[ right === {}, {}, Rest @ right ] |>
  ]

TMtoGSDecodeConfig[ gsConfig_Association, machine_Association ] :=
  Module[ { cells = gsConfig[ "cells" ], k = machine[ "numSymbols" ],
            leftCell, mid, rightCell, state, color },
    If[ Length @ cells =!= 3, Return @ Missing[ "malformed-window" ] ];
    { leftCell, mid, rightCell } = cells;
    If[ mid < k,
      <| "state" -> 0, "left" -> Prepend[ gsConfig[ "left" ], leftCell ],
         "head" -> mid, "right" -> Prepend[ gsConfig[ "right" ], rightCell ] |>,
      { state, color } = TMtoGSDecodeActive[ mid, k ];
      <| "state" -> state, "left" -> Prepend[ gsConfig[ "left" ], leftCell ],
         "head" -> color, "right" -> Prepend[ gsConfig[ "right" ], rightCell ] |>
    ]
  ]

TMtoGSMachine[ machine_Association ] :=
  Module[ { k = machine[ "numSymbols" ], s = machine[ "numStates" ] },
    <| "alphabet" -> s * k + k,
       "width" -> 3,
       "active" -> Function[ window,
         Length @ window === 3 && window[[ 2 ]] >= k ],
       "transition" -> Function[ window,
         Module[ { leftCell, mid, rightCell, decoded, state, color, rule },
           { leftCell, mid, rightCell } = window;
           decoded = TMtoGSDecodeActive[ mid, k ];
           { state, color } = decoded;
           rule = machine[ "transition" ][ { state, color } ];
           Which[
             rule[ "direction" ] === "L" && rule[ "nextState" ] == 0,
               <| "replacement" -> { leftCell, rule[ "write" ], rightCell },
                  "magnitude" -> 1, "shiftLeft" -> True |>,
             rule[ "direction" ] === "L",
               <| "replacement" ->
                    { TMtoGSEncodeActive[ rule[ "nextState" ], leftCell, k ],
                      rule[ "write" ], rightCell },
                  "magnitude" -> 1, "shiftLeft" -> True |>,
             rule[ "direction" ] === "R" && rule[ "nextState" ] == 0,
               <| "replacement" -> { leftCell, rule[ "write" ], rightCell },
                  "magnitude" -> 1, "shiftLeft" -> False |>,
             rule[ "direction" ] === "R",
               <| "replacement" ->
                    { leftCell, rule[ "write" ],
                      TMtoGSEncodeActive[ rule[ "nextState" ], rightCell, k ] },
                  "magnitude" -> 1, "shiftLeft" -> False |>
           ]
         ]
       ]
    |>
  ]

(* ──────────────────────────────────────────────────────────────────────────
   GS \[RightArrow] TM  (Moore Theorem 8)
   ────────────────────────────────────────────────────────────────────────── *)

GStoTMEncodeConfig[ gsConfig_Association ] :=
  Module[ { cells = gsConfig[ "cells" ], head, tail },
    If[ cells === {},
      <| "state" -> 1, "left" -> gsConfig[ "left" ], "head" -> 0,
         "right" -> gsConfig[ "right" ] |>,
      head = First @ cells; tail = Rest @ cells;
      <| "state" -> 1, "left" -> gsConfig[ "left" ], "head" -> head,
         "right" -> Join[ tail, gsConfig[ "right" ] ] |>
    ]
  ]

GStoTMDecodeConfigPadded[ tmConfig_Association, w_Integer ] :=
  Module[ { right = tmConfig[ "right" ], prefix, padLength, cells },
    If[ tmConfig[ "state" ] =!= 1, Return @ Missing[ "non-state-1" ] ];
    prefix = Take[ right, UpTo[ w - 1 ] ];
    padLength = ( w - 1 ) - Length @ prefix;
    cells = Prepend[ Join[ prefix, ConstantArray[ 0, padLength ] ],
                     tmConfig[ "head" ] ];
    <| "left" -> tmConfig[ "left" ], "cells" -> cells,
       "right" -> Drop[ right, UpTo[ w - 1 ] ] |>
  ]

(* TM phase encoding (matches Lean's TMPhase \[Leftrightarrow] Nat bijection). *)

readState[ pos_, partialCode_, gsParams_ ] :=
  2 + pos * gsParams[ "alphabet" ]^gsParams[ "width" ] + partialCode

writeStateBase[ gsParams_ ] :=
  2 + gsParams[ "width" ] * gsParams[ "alphabet" ]^gsParams[ "width" ]

writeState[ pos_, windowCode_, gsParams_ ] :=
  writeStateBase[ gsParams ] +
    pos * gsParams[ "alphabet" ]^gsParams[ "width" ] + windowCode

shiftStateBase[ gsParams_ ] :=
  writeStateBase[ gsParams ] +
    gsParams[ "width" ] * gsParams[ "alphabet" ]^gsParams[ "width" ]

shiftState[ remaining_, goLeft_, gsParams_ ] :=
  shiftStateBase[ gsParams ] + remaining * 2 + If[ goLeft, 1, 0 ]

phaseToNat[ phase_, gsParams_ ] :=
  Switch[ phase[ "tag" ],
    "halt",  0,
    "start", 1,
    "read",  readState[ phase[ "pos" ], phase[ "partialCode" ], gsParams ],
    "write", writeState[ phase[ "pos" ], phase[ "windowCode" ], gsParams ],
    "shift", shiftState[ phase[ "remaining" ], phase[ "goLeft" ], gsParams ]
  ]

natToPhase[ n_Integer, gsParams_ ] :=
  Module[ { wsBase = writeStateBase[ gsParams ], shBase = shiftStateBase[ gsParams ],
            powAW = gsParams[ "alphabet" ]^gsParams[ "width" ] },
    Which[
      n == 0, <| "tag" -> "halt" |>,
      n == 1, <| "tag" -> "start" |>,
      2 <= n < wsBase,
        <| "tag" -> "read",
           "pos" -> Quotient[ n - 2, powAW ],
           "partialCode" -> Mod[ n - 2, powAW ] |>,
      wsBase <= n < shBase,
        <| "tag" -> "write",
           "pos" -> Quotient[ n - wsBase, powAW ],
           "windowCode" -> Mod[ n - wsBase, powAW ] |>,
      True,
        <| "tag" -> "shift",
           "remaining" -> Quotient[ n - shBase, 2 ],
           "goLeft" -> OddQ[ n - shBase ] |>
    ]
  ]

encodeWindow[ window_List, alpha_ ] :=
  Fold[ #1 * alpha + #2 &, 0, window ]

decodeWindow[ code_Integer, alpha_, w_ ] :=
  Module[ { c = code, acc = {} },
    Do[ PrependTo[ acc, Mod[ c, alpha ] ]; c = Quotient[ c, alpha ], { w } ];
    acc
  ]

getListElem[ list_List, idx_Integer ] :=
  If[ 0 <= idx < Length @ list, list[[ idx + 1 ]], 0 ]

startShiftPhase[ repl_, rule_, gsParams_ ] :=
  Which[
    rule[ "magnitude" ] == 0,
      { <| "tag" -> "start" |>, repl, "R" },
    rule[ "magnitude" ] == 1,
      { <| "tag" -> "start" |>, repl,
        If[ rule[ "shiftLeft" ], "L", "R" ] },
    True,
      { <| "tag" -> "shift",
           "remaining" -> rule[ "magnitude" ] - 2,
           "goLeft" -> rule[ "shiftLeft" ] |>,
        repl,
        If[ rule[ "shiftLeft" ], "L", "R" ] }
  ]

phaseTransition[ phase_, symbol_, gsParams_ ] :=
  Module[ { window, rule, newPartial, replHere },
    Switch[ phase[ "tag" ],
      "halt",
        { phase, symbol, "R" },
      "start",
        If[ gsParams[ "width" ] <= 1,
          window = { symbol };
          If[ ! gsParams[ "active" ][ window ],
            { <| "tag" -> "halt" |>, symbol, "R" },
            rule = gsParams[ "transition" ][ window ];
            startShiftPhase[ getListElem[ rule[ "replacement" ], 0 ], rule, gsParams ]
          ],
          { <| "tag" -> "read", "pos" -> 1, "partialCode" -> symbol |>, symbol, "R" }
        ],
      "read",
        newPartial = phase[ "partialCode" ] * gsParams[ "alphabet" ] + symbol;
        If[ phase[ "pos" ] + 1 >= gsParams[ "width" ],
          window = decodeWindow[ newPartial, gsParams[ "alphabet" ], gsParams[ "width" ] ];
          If[ ! gsParams[ "active" ][ window ],
            { <| "tag" -> "halt" |>, symbol, "L" },
            rule = gsParams[ "transition" ][ window ];
            replHere = getListElem[ rule[ "replacement" ], gsParams[ "width" ] - 1 ];
            If[ gsParams[ "width" ] <= 1,
              startShiftPhase[ replHere, rule, gsParams ],
              { <| "tag" -> "write",
                   "pos" -> gsParams[ "width" ] - 2,
                   "windowCode" -> newPartial |>, replHere, "L" }
            ]
          ],
          { <| "tag" -> "read", "pos" -> phase[ "pos" ] + 1,
               "partialCode" -> newPartial |>, symbol, "R" }
        ],
      "write",
        window = decodeWindow[ phase[ "windowCode" ],
                                gsParams[ "alphabet" ], gsParams[ "width" ] ];
        rule = gsParams[ "transition" ][ window ];
        replHere = getListElem[ rule[ "replacement" ], phase[ "pos" ] ];
        If[ phase[ "pos" ] == 0,
          startShiftPhase[ replHere, rule, gsParams ],
          { <| "tag" -> "write", "pos" -> phase[ "pos" ] - 1,
               "windowCode" -> phase[ "windowCode" ] |>, replHere, "L" }
        ],
      "shift",
        Module[ { dir = If[ phase[ "goLeft" ], "L", "R" ] },
          If[ phase[ "remaining" ] == 0,
            { <| "tag" -> "start" |>, symbol, dir },
            { <| "tag" -> "shift", "remaining" -> phase[ "remaining" ] - 1,
                 "goLeft" -> phase[ "goLeft" ] |>, symbol, dir }
          ]
        ]
    ]
  ]

GStoTMTemporalOverhead[ gsParams_Association ] :=
  2 * ( gsParams[ "width" ] - 1 ) + gsParams[ "maxShift" ]

GStoTMMachine[ gsParams_Association ] :=
  <|
    "numStates" -> shiftStateBase[ gsParams ] + ( gsParams[ "maxShift" ] + 1 ) * 2,
    "numSymbols" -> gsParams[ "alphabet" ],
    "transition" -> Function[ qc,
      Module[ { phase, transitionResult, nextPhase, write, dir },
        phase = natToPhase[ qc[[ 1 ]], gsParams ];
        transitionResult = phaseTransition[ phase, qc[[ 2 ]], gsParams ];
        { nextPhase, write, dir } = transitionResult;
        <| "nextState" -> phaseToNat[ nextPhase, gsParams ],
           "write" -> write, "direction" -> dir |>
      ]
    ]
  |>

End[]
EndPackage[]
