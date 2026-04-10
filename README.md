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
| TM ↔ Generalized Shift (Moore 1991) | [Wiki/Notebooks/TM_GS.md](Wiki/Notebooks/TM_GS.md) | [Wolfram Cloud](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/TM_GS.nb) |
| Cocke–Minsky Chain (TM → Tag → CTS → (2,3) TM) | [Wiki/Notebooks/CockeMinsky.md](Wiki/Notebooks/CockeMinsky.md) | [Wolfram Cloud](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/CockeMinsky.nb) |
| The Universality Graph | [Wiki/Notebooks/UniversalityGraph.md](Wiki/Notebooks/UniversalityGraph.md) | [Wolfram Cloud](https://www.wolframcloud.com/obj/hajek_pavel/UniversalityGraph/UniversalityGraph.nb) |
| Cross-Validation (Lean vs. Wolfram) | [Wiki/Notebooks/CrossValidation.md](Wiki/Notebooks/CrossValidation.md) | — |

## 📖 Wiki

Browse the **[knowledge base](Wiki/Index.md)** for articles on every system, proof, and resource in the project.

## ✅ Lean-Verified Edges (0 sorry)

| Edge | Overhead | Reference |
|---|---|---|
| TM → Generalized Shift | σ=1, τ=1 | Moore 1991, Thm 7 |
| Generalized Shift → TM | σ=1, τ≤2(w−1)+m | Moore 1991, Thm 8 (proved for w=1) |
| 2-Tag → Cyclic Tag System | σ=k (one-hot), τ=2k | Cook 2004 |
| ECA Rule 110 ↔ Rule 124 | σ=1, τ=1 | Tape reversal mirror |

### Proved modulo explicit hypotheses

| Theorem | Hypotheses | Reference |
|---|---|---|
| Wolfram's (2,3) TM is universal | Cocke-Minsky step simulation, Smith CTS→(2,3) simulation | Cocke-Minsky 1964 + Cook 2004 + Smith 2007 |

## Verification

How to verify that LLM-generated proofs in this repository are trustworthy:

```bash
Scripts/verify_integrity.sh    # CollectAxioms on key theorems + leanchecker kernel replay
```

The full trust model is documented in [Wiki/Concepts/ProofIntegrity.md](Wiki/Concepts/ProofIntegrity.md). In short: `Integrity.lean` uses Lean's `CollectAxioms` API to verify that every key theorem depends only on Lean's three standard axioms. `leanchecker` replays all declarations through the kernel independently. No grep or string parsing — all verification uses Lean's own tools.

## 🔨 Build Instructions

```bash
git clone --recurse-submodules <url>   # clone with LeanLink and TuringMachine submodules
cd Lean && lake build                  # build Lean project
Scripts/generate_notebooks.wls         # Wiki/Notebooks/*.md → Notebooks/*.nb
Scripts/recover_resources.sh           # rebuild Resources/ from Wiki/Resources/*.md
leanblueprint web                      # build interactive Blueprint
```

## 🤝 Contributing

We want to maximally utilize LLMs for keeping structure and writing proofs with only high-level human interaction. The full workflow is described in [CLAUDE.md](CLAUDE.md).

See the [action items](Wiki/Plans/ActionItems.md) for next steps.

## 📄 License

MIT
