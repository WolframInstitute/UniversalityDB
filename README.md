# 🌐 UniversalityDB

A database of [computational universality](https://en.wikipedia.org/wiki/Turing_completeness) proofs, formalized and verified in [Lean](https://lean-lang.org), validated and presented using Wolfram notebooks, all built and maintained by LLMs with only high-level expert guidance.
This is to demonstrate that LLMs can autonomously push the boundary of mathematical research if they are given the right ingredients:

- ✅ **Certification** — [Lean](https://lean-lang.org) link to formalize and verify proofs
- ⚙️ **Computational engine** — [Wolfram](https://www.wolfram.com/language/) link to prototype and test on finite examples
- 📚 **Knowledge base** — a growing structured knowledge of the previous work (universality graph, wiki)
- 🧠 **Expert guidance** — high-level guidance by members of the Wolfram Institute
- 🤖 **Agentic team member** — autonomous agent homed at a Wolfram Institute server autonomously maintaining the repo and extending the research (TBD)

The generated data is organized as a **universality graph**: vertices are computational systems (Turing machines, cellular automata, tag systems, generalized shifts, ...) and directed edges are simulation encodings (weighted by overhead). We introduce this structure to empirically study the simulability landscape across simple machines in the spirit of Wolfram's [metamathematics project](https://www.wolframphysics.org/bulletins/2022/10/physicalization-of-metamathematics/) and [principle of computational equivalence](https://www.wolframscience.com/nks/p715/).


## 📓 Notebooks

| Notebook | Source | Wolfram Cloud |
|:--|:--|:--|
| ECA Klein-4 Symmetries | [Markdown](Wiki/Notebooks/ECASymmetries.md) | [Notebook](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/ECASymmetries.nb) |
| TM ↔ Generalized Shift (Moore 1991) | [Markdown](Wiki/Notebooks/TM_GS.md) | [Notebook](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/TM_GS.nb) |
| Cocke–Minsky Chain (TM → Tag → CTS → (2,3) TM) | [Markdown](Wiki/Notebooks/CockeMinsky.md) | [Notebook](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/CockeMinsky.nb) |
| The Universality Graph | [Markdown](Wiki/Notebooks/UniversalityGraph.md) | [Notebook](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/UniversalityGraph.nb) |
| Cross-Validation (Lean vs. Wolfram) | [Markdown](Wiki/Notebooks/CrossValidation.md) | — |

## Verified Simulation Edges

Edge wrappers live in [Lean/Edges.lean](Lean/Edges.lean); each carries its hypotheses explicitly in its type. Templates (`Simulation`, `SimulationEncoding`, `HaltingSimulation`) are explained in [Wiki/Concepts/SimulationEncoding.md](Wiki/Concepts/SimulationEncoding.md).

| Edge | Overhead (σ, τ) | Template | Reference | Sorry |
|:--|:--|:--|:--|:--|
| [ECA 110 ↔ 124, 137, 193](Wiki/Proofs/ECAConjugation.md) | 1, 1 | `Simulation` | NKS p.55 | 0 |
| [TM → Generalized Shift](Wiki/Proofs/TMtoGS.md) | 1, 1 | `SimulationEncoding` | Moore 1991, Thm. 7 | 0 |
| [Generalized Shift → TM](Wiki/Proofs/GStoTM.md) | 1, ≤2(w−1)+m | `SimulationEncoding` | Moore 1991, Thm. 8 | 0 |
| [2-Tag → Cyclic Tag](Wiki/Proofs/TagToCTS.md) | k, 2k | `Simulation` | Cook 2004 | 1 |
| TM → 2-Tag | — | `Simulation` | Cocke 1964 | axiomatized as hypothesis `CockeMinskyStepSimulation` |
| Cyclic Tag → (2,3) TM | — | `HaltingSimulation` | Smith 2007 | axiomatized as hypothesis `SmithSimulation` |

The last three rows compose into [`edge_CockeMinskyChain`](Lean/Edges.lean), which gives `IsUniversal wolfram23` — universality of Wolfram's (2,3) TM, conditional on the two hypothesis arrows. See [Wiki/Proofs/CockeMinskyChain.md](Wiki/Proofs/CockeMinskyChain.md).

## Verification

1. Read the theorem type in [Lean/Edges.lean](Lean/Edges.lean) — every hypothesis is explicit.
2. Read the machine definitions in [Lean/Machines](Lean/Machines).
3. Run the script below: rebuilds, audits axiom dependencies, replays through Lean's kernel.
4. Cross-check on concrete examples in [Wiki/Notebooks/CrossValidation.md](Wiki/Notebooks/CrossValidation.md).

```bash
Scripts/verify_integrity.sh
```

Trust model: [Wiki/Concepts/ProofIntegrity.md](Wiki/Concepts/ProofIntegrity.md)

## Build

```bash
git clone --recurse-submodules <url>
cd Lean && lake build
Scripts/generate_notebooks.wls    # Wiki/Notebooks/*.md → Notebooks/*.nb
leanblueprint web                 # interactive Blueprint
```

## Contributing

Workflow: [CLAUDE.md](CLAUDE.md) · Next steps: [Wiki/Plans/ActionItems.md](Wiki/Plans/ActionItems.md)

## License

MIT
