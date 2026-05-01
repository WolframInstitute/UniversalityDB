# The Universality Graph

## Preamble

```wolfram
Get[ FileNameJoin[ { NotebookDirectory[], "..", "Wolfram", "UniversalityGraph.wl" } ] ]
```

## The Graph

Edge convention: A -> B means A embeds in B (B simulates A). Universal machines are sinks. Thick green = Lean-verified, thin gray = from literature.

```wolfram
graph = UniversalityGraphCreate[]
```

## Edge Table

```wolfram
UniversalityGraphKnownResults[]
```

## Metrics

```wolfram
UniversalityGraphMetrics[ graph ]
```

## Universal Vertices

Vertices reachable from every other vertex (everything can compile to them):

```wolfram
UniversalityGraphUniversalVertices[ graph ]
```

## Shortest Path Example

The cheapest simulation chain from CyclicTag to TM23:

```wolfram
path = UniversalityGraphShortestPath[ graph, "CyclicTag", "TM23" ];
path
```

## Path Overhead

Compose the overhead along the chain:

```wolfram
edges = UniversalityGraphKnownResults[];
pathEdges = Partition[ path, 2, 1 ];
Select[ Normal[ edges ], MemberQ[ pathEdges, { #[ "Source" ], #[ "Target" ] } ] & ]
```

## Adding a New Edge

```wolfram
newGraph = UniversalityGraphAddEdge[ graph,
  "CyclicTag", "TM23", "O[w]", "O[w^2]", "hypothetical direct proof", False ];
newGraph
```
