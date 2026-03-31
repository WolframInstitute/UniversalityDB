(* ::Package:: *)
BeginPackage[ "TagCTSEncoding`" ]

TagToCTSEncode::usage = "TagToCTSEncode[ word, k ] encodes a tag word as a CTS config {data, phase}."
TagToCTSAppendants::usage = "TagToCTSAppendants[ productions, k ] builds the 2k CTS appendants from tag productions."
SymbolEncode::usage = "SymbolEncode[ i, k ] returns the one-hot binary encoding of symbol i in alphabet of size k."

Begin[ "`Private`" ]

SymbolEncode[ i_Integer, k_Integer ] :=
  Table[ j == i, { j, 0, k - 1 } ]

TagToCTSEncode[ word_List, k_Integer ] :=
  { Flatten[ SymbolEncode[ #, k ] & /@ word ], 0 }

TagToCTSAppendants[ productions_Association, k_Integer ] :=
  Join[
    Table[ Flatten[ SymbolEncode[ #, k ] & /@ productions[ i ] ], { i, 0, k - 1 } ],
    Table[ {}, k ]
  ]

End[]
EndPackage[]
