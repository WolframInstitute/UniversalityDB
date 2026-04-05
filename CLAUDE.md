# The Universality Graph

A formally verified knowledge graph of computational universality. Vertices are computational systems (Turing machines, cellular automata, tag systems, ...). Directed edges are simulation encodings with spatial/temporal overhead, certified in Lean 4.

## Current focus

**Lean formalization of existing universality proofs.** Read a paper, formalize the machines and encoding in Lean, verify the simulation, demonstrate it in a notebook.

Future stages (basic scaffolding exists, not the priority):
- Graph construction and queries (`Wolfram/UniversalityGraph.wl`)
- Automatic extension via LLM pipeline (`Resources/pipeline_architecture.md`)
- Metamathematics exploration (higher categories, ruliad connections)

## Repository structure

```
CLAUDE.md               this file
README.md               public overview with Wolfram Cloud notebook links
lakefile.lean           symlink to Lean/lakefile.lean (required by leanblueprint)

Scripts/                shell and wolframscript utilities
  generate_notebooks.wls  convert .md -> .nb locally
  publish_notebooks.wls   convert .md -> .nb, upload to Wolfram Cloud
  recover_resources.sh    download all resource PDFs

Lean/                   entire Lean 4 project
  CompSystem.lean       base type: Config + step
  Simulation.lean       Simulation, Overhead, composition
  UniversalityGraph.lean  Graph.System, Graph.Edge registry
  lakefile.lean         Lake build config
  Machine/              parametric machine definitions (one subfolder per family)
  Proof/                simulation proofs (one file per edge)
  Proof/Edges.lean      all registered edges (imports all proofs)

Wolfram/                Wolfram Language packages (.wl only)
  Tools.wl              shared utilities
  UniversalityGraph.wl  graph construction, queries, metrics
  SimulationEncoding.wl encoding objects, overhead composition
  Encoding/             simulation encoding functions (e.g. TM_Tag.wl, Tag_CTS.wl)

Notebooks/              generated .nb files (gitignored, built from Wiki/Notebooks/*.md)

Blueprint/              Lean Blueprint (PFR-style, files at top level)
  web.tex, print.tex    drivers for web / PDF build
  references.bib        BibTeX
  chapter/              one .tex file per chapter
  preamble/             shared macros

Resources/              on-demand local directory (gitignored except submodules)
  *.pdf, *.nb           downloaded on demand via Scripts/recover_resources.sh
  LeanLink/             git submodule: WolframInstitute/LeanLink
  TuringMachine/        git submodule: WolframInstitute/TuringMachine

Wiki/                   LLM-maintained knowledge base (plain markdown)
  Index.md              master index of all articles
  Status.md             current repo state: proved, sorry'd, next steps
  Log.md                chronological log of LLM actions and human revisions
  Systems/              one article per computational system family
  Proofs/               one article per simulation proof
  Concepts/             cross-cutting concepts
  Resources/            papers, repos, notebooks, tools — anything with a download URL
  Notebooks/            .md sources for Wolfram notebooks (converted to .nb)
  Plans/                plans, roadmaps, design decisions

Tour/                   guided tour (created on demand, local, gitignored)
  Tour.md               tour plan: ordered sections, current position, progress
  Sections/             one .md per section with narrative + code references
  Code/                 generated .wl files the user can paste into notebooks
```

## Adding a new universality proof

### 1. Research the paper

Read the reference. If no wiki article exists, create `Wiki/Resources/Author_Year.md`:
- Title, author, year, short summary, download URL
- Key info: encoding, decoding, step correspondence, overhead bounds
- Update `Wiki/Index.md`

### 2. Define machines in Lean

Check `Lean/Machine/` for existing definitions. If missing, create `Lean/Machine/<Family>/Defs.lean` following `ECA/Defs.lean` or `GS/Defs.lean`. Define `Config`, `step`, helpers. Register in `Lean/lakefile.lean` roots.

### 3. Write the simulation proof

Create `Lean/Proof/<Name>.lean` following `Lean/Proof/TMtoGS.lean`:
1. Define `encode`, `decode`
2. Prove `roundtrip` and `step_commutes`
3. Add `#eval` spot checks

Use `sorry` for deferred lemmas, `native_decide` for finite checks. Register in `lakefile.lean` roots.

### 4. Register the edge

In `Lean/Proof/Edges.lean`: add `CompSystem` instance, `Edge` definition, add to `mkGraph`.

### 5. Register in Wolfram

Add to `$knownSystems` and `$knownEdges` in `Wolfram/UniversalityGraph.wl`.

### 6. Write demonstration notebook

Create `Wiki/Notebooks/<Name>.md` following `Wiki/Notebooks/TM_GS.md`. Naming: `Source_Target.md` for single edges, descriptive name for chains (e.g. `CockeMinsky.md`). Add to `Wiki/Index.md` and `README.md`.
1. Setup (LeanLink + load encoding .wl files from `Wolfram/Encoding/`)
2. Machine definitions (show Lean source)
3. Encoding (show Lean source)
4. Brief validation (use built-in `TuringMachine`, `ResourceFunction["TagSystem"]`, etc. + encoding .wl functions)
5. Lean verification (LeanImportString, inspect theorems)

### 7. Update Blueprint

Add to `Blueprint/chapter/verified.tex` with `\lean{}` and `\leanok` annotations.

### 8. Build and verify

```bash
cd Lean && lake build
./publish_notebooks.wls
leanblueprint web
```

Add the Wolfram Cloud link to `README.md`.

## Conventions

### Notebooks

Notebook sources live in `Wiki/Notebooks/*.md` (tracked in git). The `.nb` files are generated into `Notebooks/` (gitignored) via `Scripts/generate_notebooks.wls`. Published to Wolfram Cloud via `Scripts/publish_notebooks.wls`.

**README.md lists all notebooks** with three links each: the wiki `.md` source, the local `.nb` path, and the Wolfram Cloud URL (if published).

When creating a new notebook: write `Wiki/Notebooks/Name.md`, add it to `Wiki/Index.md` under Notebooks, and add it to `README.md`.

### Resources

`Resources/` is a **local, on-demand directory** (gitignored except submodules). It holds downloaded PDFs, notebooks, and other binary files. Summaries and download URLs live in `Wiki/Resources/`.

**Adding a resource:** Download the file to `Resources/`, then create `Wiki/Resources/Name.md` with a summary and a `## Recover` section containing the download URL and target path. Update `Wiki/Index.md`.

**Recovering resources:** `Scripts/recover_resources.sh` scans all `Wiki/Resources/*.md` files, parses `## Recover` sections (`Download:` → curl, `Clone:` → git clone), and rebuilds `Resources/`.

Submodules (tracked, not gitignored):
- `Resources/LeanLink/` — `WolframInstitute/LeanLink` (Lean 4 <-> WL bridge)
- `Resources/TuringMachine/` — `WolframInstitute/TuringMachine` (Lean dependency)

Clone: `git clone --recurse-submodules <url>`
Update: `git submodule update --init --recursive`

### Blueprint

When the user says "note this" or "add this", append to the appropriate `Blueprint/chapter/*.tex` file. Use `\lean{}` / `\leanok` for formalized results.

## Knowledge Base (Wiki)

The project maintains a lightweight markdown wiki in `Wiki/`. It serves as a human-readable, LLM-navigable knowledge base compiled from raw sources, activities, and the evolving state of the repo.

### Structure

```
Wiki/
  Index.md              master index — every article listed with one-line summary
  Status.md             current state of the repo: what's proved, what's sorry'd, what's next
  Systems/              one article per computational system family
  Proofs/               one article per simulation proof (edge in the graph)
  Concepts/             cross-cutting concepts (overhead, universality, encodings, ...)
  Resources/            papers, repos, notebooks, tools — anything with a download/clone URL
  Notebooks/            .md sources for Wolfram notebooks (→ Notebooks/*.nb via generate script)
  Plans/                plans, decisions, and roadmaps
  Log.md                chronological log of LLM actions and human revisions
```

Each article is a standalone `.md` file. No special tooling — just plain markdown a human can browse on GitHub or in any editor.

### Article format

```markdown
# Title

One-paragraph summary.

## Details

Body. Use subsections as needed.

## See also

- [OtherArticle](../Folder/OtherArticle.md) — why it's related
```

Backlinks use **relative markdown links** so they are clickable on GitHub. Same-folder links: `[Name](Name.md)`. Cross-folder links: `[Name](../Folder/Name.md)`. Keep articles concise — encyclopedia-style, not exhaustive.

### How the LLM maintains the wiki

**After every substantial step** (new proof, new machine definition, new resource, architecture change, key decision), update the wiki:

1. **Create or update** the relevant article(s) in the appropriate subfolder.
2. **Update `Wiki/Index.md`** — add/remove/edit the one-line entry.
3. **Update `Wiki/Status.md`** — reflect the current state (proved edges, open sorries, next steps).
4. **Add backlinks** in related articles' "See also" sections.

**Periodically run a health check** (when asked, or when starting a new session):
- Scan for stale information (articles that don't match current code).
- Identify missing articles (systems, proofs, or resources with no wiki entry).
- Find broken backlinks.
- Look for new connections worth cross-linking.

### Revision workflow

**Wiki articles are documentation** — the LLM updates them freely to keep them accurate. No human sign-off needed for wiki prose.

**Revision matters for code and functionality.** When the LLM produces new code, new features, plans, or tour sections, it must:
1. Present the work to the user.
2. Wait for feedback before considering it done.
3. If the user says "ok", "looks good", or accepts without objection — proceed.
4. If the user says "change X" — revise and re-present.

**User-edited content is protected.** If the user has explicitly written or edited something (a plan, code, a config file), the LLM does not silently overwrite it. Instead: describe what you'd change and why, then wait for approval.

### Plans

`Wiki/Plans/` contains plans, roadmaps, and design decisions. Each plan file follows this format:

```markdown
# Plan: Title

## Goal

What we're trying to achieve.

## Steps

- [ ] Step 1
- [ ] Step 2
- [x] Step 3 (completed)

## Decisions

Key choices made and why.

## History

| Date | Actor | Action |
|---|---|---|
| 2026-04-05 | LLM | Created plan |
| 2026-04-05 | Human | Revised: changed step 2 |
```

Plans are presented to the user for review (they contain decisions and code). The LLM does not silently overwrite user-edited plans. The History table tracks who did what.

### Activity log

`Wiki/Log.md` is a **reverse-chronological** log of significant actions. One line per action. The LLM appends after every substantial step. The user can annotate with revision notes.

```markdown
# Activity Log

| Date | Actor | Action |
|---|---|---|
| 2026-04-05 | LLM | Created wiki with 22 seed articles |
| 2026-04-05 | Human | Revised: added Plans/ and revision workflow |
```

### What goes into the wiki

| Source | Wiki article |
|---|---|
| Paper, repo, notebook, tool | `Wiki/Resources/Name.md` — summary, download/clone URL, how it's used here |
| Machine family in `Lean/Machines/` | `Wiki/Systems/FamilyName.md` — definition, properties, Lean module path |
| Simulation proof in `Lean/Proofs/` | `Wiki/Proofs/SourceToTarget.md` — encoding, overhead, proof status, key lemmas |
| Cross-cutting concept | `Wiki/Concepts/ConceptName.md` — definition, where it appears, connections |
| Repo-level state | `Wiki/Status.md` — proved/unproved edges, current focus, blockers |
| Roadmap / design decision | `Wiki/Plans/PlanName.md` — goal, steps, decisions, history |
| LLM and human actions | `Wiki/Log.md` — reverse-chronological one-liners |

### What does NOT go into the wiki

- Verbatim code (link to the file instead)
- Ephemeral working notes (use `working.md` for that)
- Build instructions or dev setup (that's in this file)

### Scale

At the current scale (~100 articles, ~400k words max), no vector database or embeddings are needed. The LLM navigates via `Wiki/Index.md` and the folder structure. Keep `Index.md` compact — one line per article.

## Guided Tour

The project supports an interactive **guided tour** — a curated walk through the codebase from simplest to most complex, designed for presentation, onboarding, or deep understanding. The tour lives in `Tour/` (local, gitignored).

### Starting a tour

When the user says **"start tour"**, **"give me a tour"**, or similar:

1. If `Tour/` does not exist, **create it** (`Tour/`, `Tour/Sections/`, `Tour/Code/`).
2. Read `Tour/Tour.md` if it exists (resume where we left off).
3. If no tour plan exists, generate one:
   - Read `Wiki/Index.md` and `Wiki/Status.md` to understand the current state.
   - Order topics from simplest to most complex (e.g.: ComputationalMachine → TuringMachine → GeneralizedShift → TM↔GS encoding → TagSystem → CTS → CockeMinsky chain → ECA → overhead/graph structure).
   - Write `Tour/Tour.md` with the section plan and mark position at section 1.
4. Present the first (or current) section.

### Tour structure

```
Tour/
  Tour.md               plan + current position + progress log
  Sections/
    01_ComputationalMachine.md
    02_TuringMachine.md
    ...
  Code/
    01_ComputationalMachine.wl
    02_TuringMachine.wl
    ...
```

**`Tour/Tour.md`** tracks the tour:

```markdown
# Tour Plan

## Sections

1. [x] Computational Machine — the base abstraction
2. [x] Turing Machine — definition, examples, Wolfram's (2,3) UTM  ← revised
3. [ ] Generalized Shift — window-based dynamics  ← current
4. [ ] TM ↔ GS Encoding — Moore's theorems
...

## Position

Current section: 3
Last interaction: 2026-04-05

## Log

| Date | Section | Action |
|---|---|---|
| 2026-04-05 | 1 | Presented, user approved |
| 2026-04-05 | 2 | Presented, user revised: added example |
```

### Presenting a section

For each section, the LLM:

1. **Writes `Sections/NN_Name.md`** — a narrative explanation of the topic:
   - What it is, why it matters in the project
   - Key definitions and how they connect to what came before
   - Pointers to the actual Lean/Wolfram source files (not verbatim code)

2. **Generates `Code/NN_Name.wl`** — Wolfram Language code the user can paste into a notebook:
   - Concrete examples: run a TM, step a tag system, encode a config, visualize
   - Uses the project's own packages (`Wolfram/Encoding/`, `Wolfram/Tools.wl`) and built-in steppers
   - Self-contained: includes any needed `Get[...]` or `ResourceFunction[...]` calls
   - Follows the project's WL style (see Code Style section)

3. **Presents** a summary to the user and says:
   > *"Here is section N: [Topic]. The narrative is in `Tour/Sections/NN_Name.md` and the code is in `Tour/Code/NN_Name.wl`. Please review — any feedback or changes before we move on?"*

4. **Waits for feedback.** The user may:
   - **Approve** ("ok", "next", "move on") → mark section done, advance position
   - **Revise** ("change X", "add an example of Y") → update the section and code, re-present
   - **Skip** ("skip this") → mark skipped, advance
   - **Stop** ("stop", "pause") → save position, end tour

5. **Does not advance** until the user responds. The tour is interactive.

### Revision rules for tour content

Tour sections are code + narrative — the LLM waits for user feedback before advancing. If the underlying code changes significantly, offer to regenerate affected sections.

### Resuming a tour

When the user returns and says "continue tour" or "where were we":
- Read `Tour/Tour.md`, find the current position, and present that section.
- If all sections are done, offer to regenerate with updated content or deeper topics.

## Build commands

| Command | Purpose |
|---|---|
| `cd Lean && lake build` | Build Lean project |
| `Scripts/generate_notebooks.wls` | Convert `Wiki/Notebooks/*.md` → `Notebooks/*.nb` locally |
| `Scripts/publish_notebooks.wls` | Convert + upload to Wolfram Cloud |
| `Scripts/recover_resources.sh` | Rebuild `Resources/` from `Wiki/Resources/*.md` `## Recover` sections |
| `leanblueprint web` | Build interactive Blueprint |
| `leanblueprint serve` | Serve Blueprint locally |
| `cd Blueprint && pdflatex print.tex` | Build Blueprint PDF |

## Lean quick reference

**Build:** `cd Lean && lake build`

**Dependency:** `OneSidedTM` from `Resources/TuringMachine/Proofs`

**Adding a module:** add to `roots` in `Lean/lakefile.lean`

**Key types:** `CompSystem` (Config + step), `Simulation A B` (encode + decode + roundtrip + commutes), `Overhead` (spatial + temporal), `Graph.Edge`

**Common tactics:** `native_decide`, `fin_cases`, `decide`, `omega`, `sorry`

## LeanLink loading

```wolfram
SetEnvironment[ "PATH" -> Environment[ "PATH" ] <> ":" <> FileNameJoin[ { $HomeDirectory, ".elan", "bin" } ] ]
PacletDirectoryLoad[ FileNameJoin[ { NotebookDirectory[], "..", "Resources", "LeanLink", "LeanLink" } ] ];
Get[ "LeanLink`" ]
```

Key: `LeanImportString`, `env["Constants"]`, `env["TypeOf", name]["TypeForm"]`, `env["TypeOf", name]["ExprGraph"]`

## Wolfram code

**Use built-in functions and Wolfram Function Repository first.** Do not reimplement machine steppers that already exist. Only write custom code for simulation encodings (encode/decode between systems) which do not exist in any standard library.

Available steppers (use these, do not reimplement):
- `TuringMachine[rule, init, t]` — built-in
- `CellularAutomaton[rule, init, t]` — built-in
- `ResourceFunction["GeneralizedShift"]` — TM conversion + stepping
- `ResourceFunction["TagSystem"]` / `ResourceFunction["TagSystemEvolveList"]`
- `ResourceFunction["CyclicTagSystem"]`
- `ResourceFunction["CombinatorEvolveList"]`

Encoding functions in `Wolfram/Encoding/` — simulation encode/decode between systems.

Graph-level code: `Wolfram/UniversalityGraph.wl` (construction, queries), `Wolfram/SimulationEncoding.wl` (overhead composition).
