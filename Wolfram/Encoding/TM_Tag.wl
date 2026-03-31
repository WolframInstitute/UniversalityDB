(* ::Package:: *)
BeginPackage[ "TMTagEncoding`" ]

CockeMinskyEncode::usage = "CockeMinskyEncode[ {tape, head, state}, numStates, numColors ] encodes a TM config as a tag word."
CockeMinskyTagSize::usage = "CockeMinskyTagSize[ numStates, numColors ] returns the tag alphabet size."
CockeMinskyProductions::usage = "CockeMinskyProductions[ tmRules, numStates, numColors ] returns the tag productions."

Begin[ "`Private`" ]

CockeMinskyTagSize[ numStates_, numColors_ ] :=
  numStates * numColors + numColors + 1

CockeMinskyEncode[ { tape_List, head_Integer, state_Integer }, numStates_, numColors_ ] :=
  Module[ { sk = numStates * numColors, k = numColors },
    If[ state == 0, {},
      Join[
        { (state - 1) * k + tape[[ head ]] },
        (sk + # &) /@ tape[[ head + 1 ;; ]],
        { sk + k },
        (sk + # &) /@ Reverse[ tape[[ ;; head - 1 ]] ]
      ]
    ]
  ]

CockeMinskyProductions[ tmRules_List, numStates_, numColors_ ] :=
  Module[ { sk = numStates * numColors, k = numColors, prods = <||> },
    Do[
      Module[ { rule = { q, a } /. tmRules },
        prods[ (q - 1) * k + a ] =
          If[ rule[[ 1 ]] == 0, {},
            { sk + rule[[ 2 ]], (rule[[ 1 ]] - 1) * k + a } ]
      ],
      { q, numStates }, { a, 0, numColors - 1 }
    ];
    Do[ prods[ sk + a ] = { sk + a }, { a, 0, numColors - 1 } ];
    prods[ sk + k ] = { sk + k };
    prods
  ]

End[]
EndPackage[]
