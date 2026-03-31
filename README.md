# 🌐 UniversalityDB

A database of [computational universality](https://en.wikipedia.org/wiki/Turing_completeness) proofs, formalized and verified in [Lean](https://lean-lang.org), built and maintained with the help of LLMs.

The data is organized as a **universality graph**: vertices are computational systems (Turing machines, cellular automata, tag systems, generalized shifts, ...) and directed edges are simulation encodings (weighted by overhead). We introduce this structure to empirically study the simulability landscape across simple machines in the spirit of Wolfram's [metamathematics project](https://www.wolframphysics.org/bulletins/2022/10/physicalization-of-metamathematics/) and [principle of computational equivalence](https://www.wolframscience.com/nks/p715/).

The project also explores whether LLMs can autonomously push the boundary of research if they are given the right ingredients:

- ✅ **Certification** — link to [Lean](https://lean-lang.org) to formalize and verify proofs
- ⚙️ **Computational engine** — link to [Wolfram Language](https://www.wolfram.com/language/) to prototype and test on finite examples
- 📚 **Knowledge base** — a growing structured knowledge of the previous work (universality graph)
- 🧠 **Expert guidance** — high-level guidance by mathematicians and AI researchers at the Wolfram Institute

## 📓 Presentation Notebooks

> **Note:** These notebooks predate the current Lean formalization and may not reflect the latest machine definitions and proofs. They will be updated in a future release.

- [TM ↔ Generalized Shift](https://www.wolframcloud.com/obj/hajek_pavel@outlook.de/UniversalityGraph/TM_GS.nb) — Moore 1991
- [Cocke–Minsky Chain](https://www.wolframcloud.com/obj/hajek_pavel@outlook.de/UniversalityGraph/CockeMinsky.nb) — TM → Tag → CTS → (2,3) TM
- [The Universality Graph](https://www.wolframcloud.com/obj/hajek_pavel@outlook.de/UniversalityGraph/UniversalityGraph.nb)

## 🔨 Build Instructions

```bash
git clone --recurse-submodules <url>   # clone with LeanLink and TuringMachine submodules
cd Lean && lake build                  # build Lean project
Scripts/generate_notebooks.wls         # convert .md -> .nb locally
Scripts/recover_resources.sh           # download resource PDFs
leanblueprint web                      # build interactive Blueprint
```

## 🤝 Contributing

We want to maximally utilize LLMs for keeping structure and writing proofs with only high-level human interaction. The full workflow shall be descirbed and perfected in [CLAUDE.md](CLAUDE.md).

## 📄 License

MIT
