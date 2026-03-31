(* ::Package:: *)
BeginPackage[ "SimulationEncoding`" ]

SimulationEncodingCreate::usage = "SimulationEncodingCreate[ source, target, sigma, tau, ref ] creates a simulation encoding object."
SimulationEncodingCompose::usage = "SimulationEncodingCompose[ enc1, enc2 ] composes two encodings (enc1 then enc2)."
SimulationEncodingSpatialOverhead::usage = "SimulationEncodingSpatialOverhead[ enc ] returns the spatial overhead sigma."
SimulationEncodingTemporalOverhead::usage = "SimulationEncodingTemporalOverhead[ enc ] returns the temporal overhead tau."
SimulationEncodingScalarWeight::usage = "SimulationEncodingScalarWeight[ enc ] returns log(sigma * tau)."
SimulationEncodingKnownTable::usage = "SimulationEncodingKnownTable[] returns all known encodings as a Dataset."
SimulationEncodingChainOverhead::usage = "SimulationEncodingChainOverhead[ {enc1, enc2, ...} ] computes total overhead along a chain."
SimulationEncodingAsymmetryQ::usage = "SimulationEncodingAsymmetryQ[ enc1, enc2 ] tests whether overhead A->B differs from B->A."

Begin[ "`Private`" ]

(* Encoding object: Association *)
SimulationEncodingCreate[ source_String, target_String, sigma_, tau_, ref_String ] :=
  Association[
    "Source" -> source, "Target" -> target,
    "Sigma" -> sigma, "Tau" -> tau,
    "Reference" -> ref,
    "ScalarWeight" -> Log[ toNum[ sigma ] * toNum[ tau ] ] // N
  ]

toNum[ n_?NumericQ ] := N[ n ]
toNum[ "O[1]" ] := 1.
toNum[ "O[n]" ] := 10.
toNum[ "O[n^2]" ] := 100.
toNum[ "O[w]" ] := 10.
toNum[ "O[2^n]" ] := 1000.
toNum[ s_String ] := 10.

SimulationEncodingSpatialOverhead[ enc_Association ] :=
  enc[ "Sigma" ]

SimulationEncodingTemporalOverhead[ enc_Association ] :=
  enc[ "Tau" ]

SimulationEncodingScalarWeight[ enc_Association ] :=
  enc[ "ScalarWeight" ]

SimulationEncodingCompose[ enc1_Association, enc2_Association ] :=
  Module[ { sigma, tau },
    sigma = toNum[ enc1[ "Sigma" ] ] * toNum[ enc2[ "Sigma" ] ];
    tau = toNum[ enc1[ "Tau" ] ] * toNum[ enc2[ "Sigma" ] ] * toNum[ enc2[ "Tau" ] ];
    Association[
      "Source" -> enc1[ "Source" ], "Target" -> enc2[ "Target" ],
      "Sigma" -> sigma, "Tau" -> tau,
      "Reference" -> enc1[ "Reference" ] <> " + " <> enc2[ "Reference" ],
      "ScalarWeight" -> Log[ sigma * tau ] // N
    ]
  ]

SimulationEncodingChainOverhead[ encodings_List ] :=
  Fold[ SimulationEncodingCompose, encodings ]

SimulationEncodingAsymmetryQ[ enc1_Association, enc2_Association ] :=
  enc1[ "ScalarWeight" ] =!= enc2[ "ScalarWeight" ]

$knownEncodings = {
  SimulationEncodingCreate[ "Rule110", "CyclicTag", 20, "O[n]", "Cook 2004" ],
  SimulationEncodingCreate[ "CyclicTag", "2Tag", 1, "O[2^n]", "Cocke-Minsky 1964" ],
  SimulationEncodingCreate[ "CyclicTag", "ClockwiseTM", "O[n]", "O[n]", "Neary-Woods 2006" ],
  SimulationEncodingCreate[ "ClockwiseTM", "GenericTM", "O[1]", "O[n]", "Neary-Woods 2006" ],
  SimulationEncodingCreate[ "TM23", "Rule110", "O[w]", "O[w]", "Smith 2007" ],
  SimulationEncodingCreate[ "GameOfLife", "GenericTM", 1000, 1, "Rendell 2002" ],
  SimulationEncodingCreate[ "RegisterMachine", "GenericTM", 1, 1, "folklore" ],
  SimulationEncodingCreate[ "SKCombinators", "GenericTM", "O[n]", "O[n^2]", "Curry-Schoenfinkel" ],
  SimulationEncodingCreate[ "Minsky74TM", "GenericTM", "O[1]", "O[n^2]", "Minsky 1967" ],
  SimulationEncodingCreate[ "Wolfram25TM", "GenericTM", "O[w]", "O[w]", "Wolfram NKS 2002" ],
  SimulationEncodingCreate[ "19ColorNNCA", "GenericTM", 20, 1, "Wolfram NKS 2002" ]
};

SimulationEncodingKnownTable[] :=
  Dataset[ $knownEncodings ]

End[]
EndPackage[]
