# 🌐 UniversalityDB

A database of [computational universality](https://en.wikipedia.org/wiki/Turing_completeness) proofs, formalized and verified in [Lean](https://lean-lang.org), built and maintained with the help of LLMs.

The data is organized as a **universality graph**: vertices are computational systems (Turing machines, cellular automata, tag systems, generalized shifts, ...) and directed edges are simulation encodings (weighted by overhead). We introduce this structure to empirically study the simulability landscape across simple machines in the spirit of Wolfram's [metamathematics project](https://www.wolframphysics.org/bulletins/2022/10/physicalization-of-metamathematics/) and [principle of computational equivalence](https://www.wolframscience.com/nks/p715/).

The project also explores whether LLMs can autonomously push the boundary of research if they are given the right ingredients:

- ✅ **Certification** — link to [Lean](https://lean-lang.org) to formalize and verify proofs
- ⚙️ **Computational engine** — link to [Wolfram Language](https://www.wolfram.com/language/) to prototype and test on finite examples
- 📚 **Knowledge base** — a growing structured knowledge of the previous work (universality graph)
- 🧠 **Expert guidance** — high-level guidance by mathematicians and AI researchers at the Wolfram Institute

## 📓 Notebooks

| Notebook | Source | Cloud |
|---|---|---|
| TM ↔ Generalized Shift (Moore 1991) | [Wiki/Notebooks/TM_GS.md](Wiki/Notebooks/TM_GS.md) | [Cloud](https://www.wolframcloud.com/obj/hajek_pavel@outlook.de/UniversalityGraph/TM_GS.nb) |
| Cocke–Minsky Chain (TM → Tag → CTS → (2,3) TM) | [Wiki/Notebooks/CockeMinsky.md](Wiki/Notebooks/CockeMinsky.md) | [Cloud](https://www.wolframcloud.com/obj/hajek_pavel@outlook.de/UniversalityGraph/CockeMinsky.nb) |
| The Universality Graph | [Wiki/Notebooks/UniversalityGraph.md](Wiki/Notebooks/UniversalityGraph.md) | [Cloud](https://www.wolframcloud.com/obj/hajek_pavel@outlook.de/UniversalityGraph/UniversalityGraph.nb) |

## 📖 Wiki

Browse the **[knowledge base](Wiki/Index.md)** for articles on every system, proof, and resource in the project.

## 🔨 Build Instructions

```bash
git clone --recurse-submodules <url>   # clone with LeanLink and TuringMachine submodules
cd Lean && lake build                  # build Lean project
Scripts/generate_notebooks.wls         # Wiki/Notebooks/*.md → Notebooks/*.nb
Scripts/recover_resources.sh           # rebuild Resources/ from Wiki/Resources/*.md
leanblueprint web                      # build interactive Blueprint
```

## 🤝 Contributing

We want to maximally utilize LLMs for keeping structure and writing proofs with only high-level human interaction. The full workflow shall be descirbed and perfected in [CLAUDE.md](CLAUDE.md).

## 📄 License

MIT
