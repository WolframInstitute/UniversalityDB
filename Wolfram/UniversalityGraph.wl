(* ::Package:: *)
BeginPackage[ "UniversalityGraph`" ]

UniversalityGraphCreate::usage = "UniversalityGraphCreate[] builds the universality graph from known results."
UniversalityGraphAddVertex::usage = "UniversalityGraphAddVertex[ graph, name, type ] adds a computational system."
UniversalityGraphAddEdge::usage = "UniversalityGraphAddEdge[ graph, source, target, data ] adds a simulation edge."
UniversalityGraphKnownResults::usage = "UniversalityGraphKnownResults[] returns the edge table as a Dataset."
UniversalityGraphShortestPath::usage = "UniversalityGraphShortestPath[ graph, source, target ] finds minimum-overhead path."
UniversalityGraphUniversalVertices::usage = "UniversalityGraphUniversalVertices[ graph ] returns vertices reachable from all others."
UniversalityGraphMetrics::usage = "UniversalityGraphMetrics[ graph ] computes diameter, centrality, SCC."
UniversalityGraphOverheadCompose::usage = "UniversalityGraphOverheadCompose[ {s1,t1}, {s2,t2} ] composes overhead."
UniversalityGraphScalarWeight::usage = "UniversalityGraphScalarWeight[ sigma, tau ] returns log(sigma * tau)."

Begin[ "`Private`" ]

(* EDGE CONVENTION:  A -> B  means  "A is embedded in B"
   i.e. B simulates A.  The overhead (sigma, tau) is the cost of
   running A on B.  A universal machine U has a path from every
   other vertex to U. *)

(* Known computational systems: {name, type} *)
$knownSystems = {
  { "Rule110", "CA" },
  { "Rule124", "CA" },
  { "Rule137", "CA" },
  { "CyclicTag", "TagSystem" },
  { "2Tag", "TagSystem" },
  { "ClockwiseTM", "TM" },
  { "TM23", "TM" },
  { "GameOfLife", "CA" },
  { "GenericTM", "TM" },
  { "RegisterMachine", "RegisterMachine" },
  { "SKCombinators", "Combinator" },
  { "Minsky74TM", "TM" },
  { "Wolfram25TM", "TM" },
  { "19ColorNNCA", "CA" },
  { "GeneralizedShift", "GS" },
  { "PlanarBilliard", "Billiard" }
};

(* Edge format: { source, target, sigma, tau, reference, leanVerified }
   source -> target = source embeds in target = target simulates source *)

$knownEdges = {
  (* -- Literature (not yet Lean-formalized) -- *)
  { "CyclicTag", "Rule110", 20, "O[n]",
    "Cook 2004, Complex Systems 15(1) 1-40", False },
  { "GenericTM", "2Tag", 1, "O[2^n]",
    "Cocke-Minsky 1964, J. ACM 11(1) 15-20", False },
  { "GenericTM", "ClockwiseTM", "O[1]", "O[n]",
    "Neary-Woods 2006, ICALP, LNCS 4051", False },
  { "ClockwiseTM", "CyclicTag", "O[n]", "O[n]",
    "Neary-Woods 2006, ICALP, LNCS 4051", False },
  { "Rule110", "TM23", "O[w]", "O[w]",
    "Smith 2007, Wolfram Science Prize", False },
  { "GenericTM", "GameOfLife", 1000, 1,
    "Rendell 2002, in Collision-Based Computing, Springer", False },
  { "GenericTM", "RegisterMachine", 1, 1,
    "folklore (standard construction)", False },
  { "GenericTM", "SKCombinators", "O[n]", "O[n^2]",
    "Curry-Schoenfinkel (standard)", False },
  { "GenericTM", "Minsky74TM", "O[1]", "O[n^2]",
    "Minsky 1967, Computation: Finite and Infinite Machines", False },
  { "GenericTM", "Wolfram25TM", "O[w]", "O[w]",
    "Wolfram 2002, A New Kind of Science", False },
  { "GenericTM", "19ColorNNCA", 20, 1,
    "Wolfram 2002, A New Kind of Science", False },
  { "GenericTM", "PlanarBilliard", "O[1]", "O[|Q|]",
    "Miranda-Ramos 2025, arXiv:2512.19156", False },

  (* -- Lean-verified in this project -- *)
  { "Rule110", "Rule124", 1, 1,
    "Mirror conjugation", True },
  { "Rule124", "Rule110", 1, 1,
    "Mirror conjugation", True },
  { "Rule110", "Rule137", 1, 1,
    "Complement conjugation", True },
  { "Rule137", "Rule110", 1, 1,
    "Complement conjugation", True },
  { "2Tag", "CyclicTag", "O[k]", "O[k]",
    "Cook 2004, one-hot encoding", True },
  { "GenericTM", "GeneralizedShift", 1, 1,
    "Moore 1991, Nonlinearity 4, Thm 7", True },
  { "GeneralizedShift", "GenericTM", 1, "O[w]",
    "Moore 1991, Nonlinearity 4, Thm 8", True }
};

UniversalityGraphKnownResults[] :=
  Dataset[ Association[
    "Source" -> #[[1]], "Target" -> #[[2]],
    "Sigma" -> #[[3]], "Tau" -> #[[4]],
    "Reference" -> #[[5]], "LeanVerified" -> #[[6]]
  ] & /@ $knownEdges ]

scalarWeight[ sigma_, tau_ ] :=
  Log[ toNumeric[ sigma ] * toNumeric[ tau ] ] // N

toNumeric[ n_Integer ] := n
toNumeric[ n_Real ] := n
toNumeric[ "O[1]" ] := 1
toNumeric[ "O[n]" ] := 10
toNumeric[ "O[n^2]" ] := 100
toNumeric[ "O[w]" ] := 10
toNumeric[ "O[2^n]" ] := 1000
toNumeric[ s_String ] := 10

UniversalityGraphScalarWeight[ sigma_, tau_ ] :=
  scalarWeight[ sigma, tau ]

UniversalityGraphOverheadCompose[ { sigma1_, tau1_ }, { sigma2_, tau2_ } ] :=
  { sigma1 * sigma2, tau1 * sigma2 * tau2 }

$typeColors = Association[
  "TM" -> RGBColor[ 0.7, 0.85, 1.0 ],
  "CA" -> RGBColor[ 1.0, 0.85, 0.7 ],
  "TagSystem" -> RGBColor[ 0.8, 1.0, 0.8 ],
  "RegisterMachine" -> RGBColor[ 1.0, 0.8, 1.0 ],
  "Combinator" -> RGBColor[ 1.0, 1.0, 0.75 ],
  "GS" -> RGBColor[ 0.85, 0.75, 1.0 ],
  "Billiard" -> RGBColor[ 1.0, 0.75, 0.75 ]
];

systemType[ name_String ] :=
  Module[ { match },
    match = Select[ $knownSystems, #[[1]] === name & ];
    If[ match === {}, "Unknown", match[[1, 2]] ]
  ]

UniversalityGraphCreate[] :=
  Module[ { vertices, edges, weights, verified, edgeStyles },
    vertices = Union @@ ( { #[[1]], #[[2]] } & /@ $knownEdges );
    edges = DirectedEdge[ #[[1]], #[[2]] ] & /@ $knownEdges;
    weights = scalarWeight[ #[[3]], #[[4]] ] & /@ $knownEdges;
    verified = #[[6]] & /@ $knownEdges;
    edgeStyles = MapThread[
      #1 -> If[ #2,
        Directive[ Thick, RGBColor[ 0.2, 0.5, 0.2 ] ],
        Directive[ Thin, GrayLevel[ 0.5 ] ]
      ] &,
      { edges, verified }
    ];
    Graph[ vertices, edges,
      EdgeWeight -> weights,
      EdgeStyle -> edgeStyles,
      EdgeLabels -> Thread[ edges -> ( #[[5]] & /@ $knownEdges ) ],
      VertexStyle -> ( # -> $typeColors[ systemType[ # ] ] & /@ vertices ),
      VertexSize -> 0.5,
      VertexLabels -> Placed[ "Name", Center ],
      VertexLabelStyle -> Directive[ 7, Bold ],
      EdgeShapeFunction -> GraphElementData[ "FilledArrow", "ArrowSize" -> 0.02 ],
      GraphLayout -> "SpringElectricalEmbedding",
      ImageSize -> 600
    ]
  ]

UniversalityGraphAddVertex[ graph_Graph, name_String, type_String ] :=
  VertexAdd[ graph, Property[ name, { "SystemType" -> type } ] ]

UniversalityGraphAddEdge[ graph_Graph, source_String, target_String, sigma_, tau_, ref_String, verified_:False ] :=
  Module[ { edge = DirectedEdge[ source, target ], weight },
    weight = scalarWeight[ sigma, tau ];
    EdgeAdd[ graph, Property[ edge, {
      EdgeWeight -> weight, "Sigma" -> sigma, "Tau" -> tau,
      "Reference" -> ref, "LeanVerified" -> verified,
      EdgeStyle -> If[ verified,
        Directive[ Thick, RGBColor[ 0.2, 0.5, 0.2 ] ],
        Directive[ Thin, GrayLevel[ 0.5 ] ]
      ]
    } ] ]
  ]

UniversalityGraphShortestPath[ graph_Graph, source_, target_ ] :=
  FindShortestPath[ graph, source, target, Method -> "Dijkstra" ]

UniversalityGraphUniversalVertices[ graph_Graph ] :=
  Module[ { vertices },
    vertices = VertexList[ graph ];
    Select[ vertices,
      { target } |-> AllTrue[ vertices, { source } |-> (
        source === target || GraphDistance[ graph, source, target ] < Infinity
      ) ]
    ]
  ]

UniversalityGraphMetrics[ graph_Graph ] :=
  Association[
    "VertexCount" -> VertexCount[ graph ],
    "EdgeCount" -> EdgeCount[ graph ],
    "Diameter" -> GraphDiameter[ graph ],
    "SCCs" -> ConnectedComponents[ graph, Method -> "StronglyConnected" ],
    "BetweennessCentrality" -> AssociationThread[
      VertexList[ graph ],
      BetweennessCentrality[ graph ]
    ]
  ]

End[]
EndPackage[]
