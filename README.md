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
|---|---|---|
| ECA Klein-4 Symmetries | [Wiki](Wiki/Notebooks/ECASymmetries.md) | [Cloud](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/ECASymmetries.nb) |
| TM ↔ Generalized Shift (Moore 1991) | [Wiki](Wiki/Notebooks/TM_GS.md) | [Cloud](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/TM_GS.nb) |
| Cocke–Minsky Chain (TM → Tag → CTS → (2,3) TM) | [Wiki](Wiki/Notebooks/CockeMinsky.md) | [Cloud](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/CockeMinsky.nb) |
| The Universality Graph | [Wiki](Wiki/Notebooks/UniversalityGraph.md) | [Cloud](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/UniversalityGraph.nb) |
| Cross-Validation (Lean vs. Wolfram) | [Wiki](Wiki/Notebooks/CrossValidation.md) | — |

## Verified Simulation Edges

Edges use one of three templates from [`Lean/SimulationEncoding.lean`](Lean/SimulationEncoding.lean):

- `HaltingSimulation` — halting preservation only
- `Simulation` — encode + step correspondence + halting; composable
- `SimulationEncoding` — conjugation form `step_B(b) = decode(step_A^n(encode b))`

| Edge | Overhead | Template | Reference | Unproved |
|---|---|---|---|---|
| ECA Rule 110 ↔ 124, 137, 193 | σ=1, τ=1 | `Simulation` | Folklore | 0 |
| TM → Generalized Shift | σ=1, τ=1 | `SimulationEncoding` | Moore 1991 | 0 |
| Generalized Shift → TM | σ=1, τ≤2(w−1)+m | `SimulationEncoding` | Moore 1991 | 0 |
| 2-Tag → Cyclic Tag System | σ=k, τ=2k | `Simulation` | Cook 2004 | 1 |

Wolfram's (2,3) TM is universal ([`IsUniversal`](Lean/Proofs/CockeMinsky.lean)) modulo two stated hypotheses: `CockeMinskyStepSimulation` (every TM simulates via the Cocke–Minsky chain) and `SmithSimulation` (Smith 2007).

## Verification

```bash
Scripts/verify_integrity.sh    # axiom audit (CollectAxioms) + kernel replay (leanchecker)
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
