# Plan: Computational Research Plugin

## Goal

Extract the LLM workflow from UniversalityDB into the `computational-research` Claude Code plugin so it can be used in any research repo. The plugin provides: a markdown wiki (knowledge base), a human revision workflow for code and new functionality, a guided tour system, resource management, notebook generation, and activity logging.

---

## Skills to create

### 1. `wiki-init` — Initialize knowledge base

**Trigger:** "init wiki", "set up knowledge base", "add wiki to this repo"

**What it does:**
1. Create `Wiki/` directory with subfolders and seed files
2. Add wiki section to CLAUDE.md (or create it)
3. Add `Tour/` and `Resources/` (if applicable) to .gitignore
4. Scan the repo to seed initial articles

**Folder structure created:**
```
Wiki/
  Index.md          master index — one line per article
  Status.md         current repo state (what's done, what's in progress, blockers)
  Log.md            reverse-chronological activity log
  Concepts/         cross-cutting concepts, abstractions, design patterns
  Resources/        papers, repos, tools, datasets — anything with a URL
  Plans/            roadmaps, design decisions, task breakdowns
  <Domain>/         domain-specific folders (user chooses at init time)
```

The `<Domain>/` folders are project-specific. Examples:
- Math project: `Systems/`, `Proofs/`, `Theorems/`
- Software project: `Architecture/`, `APIs/`, `Modules/`
- Research project: `Experiments/`, `Methods/`, `Datasets/`

**Index.md format:**
```markdown
# Wiki Index

Knowledge base for [project]. Updated after each substantial step.
All articles are **draft** until reviewed — see revision workflow.

## Status & Log
- [Status](Status.md) — current state
- [Activity Log](Log.md) — what happened and when

## Plans
- [Plan Name](Plans/PlanName.md) — one-line summary
...

## [Domain Section]
- [Article](Domain/Article.md) — one-line summary
...
```

---

### 2. `wiki-update` — Update wiki after a change

**Trigger:** After any substantial step (automatically, or "update wiki", "log this")

**What it does:**
1. Read `Wiki/Index.md` to understand current state
2. Create or update relevant article(s) — wiki is documentation, update freely
3. Update `Wiki/Index.md` with new/changed entries
4. Update `Wiki/Status.md` if project state changed
5. Append to `Wiki/Log.md`
6. Add `[[backlinks]]` in related articles' "See also" sections

**Article format:**
```markdown
# Title

One-paragraph summary.

## Details

Body. Use subsections as needed.

## See also

- [[OtherArticle]] — why it's related
```

No status headers on wiki articles — they're documentation, maintained automatically.

---

### 3. `wiki-health` — Run health check

**Trigger:** "check wiki", "wiki health", start of new session

**What it does:**
1. Scan for stale articles (content doesn't match current code/state) — fix them
2. Find missing articles (repo entities with no wiki entry) — create them
3. Detect broken `[[backlinks]]` — fix them
4. Identify new connections worth cross-linking
5. Check `Wiki/Resources/` recover URLs are still valid
6. Report summary to user

---

### 4. `revise` — Human revision workflow for code and functionality

**Trigger:** After LLM produces code, new functionality, a plan, or any deliverable

**The core loop:**

The LLM generates → presents to the user → **waits for feedback** → user revises or approves → only then is it considered done. This applies to:

- **Code** (Lean proofs, Wolfram functions, scripts)
- **New functionality** (new machine definitions, encodings, graph edges)
- **Plans** (what to do next, architecture decisions)
- **Tour sections** (narrative + code for presentation)

**What "revision" means:**

The LLM should always make the user aware of what it produced and actively seek feedback. The user responding "ok", "looks good", "next", or accepting without objection counts as approval. The user saying "change X" or "no, do Y instead" means revise and re-present.

**What revision does NOT mean:**

Wiki article prose does not need individual human sign-off. The wiki is documentation — the LLM keeps it accurate and up-to-date automatically. If an article becomes wrong because code changed, just fix it. No ceremony needed for wiki text.

**What gets protected:**

When the user has explicitly edited or rewritten something (a plan, a design decision, a piece of code), the LLM should not silently overwrite it. Instead: describe what you'd change and why, then wait for approval. This applies to:
- User-edited plans in `Wiki/Plans/`
- User-written code or config
- Anything the user explicitly crafted

**Log everything:** Every LLM action and every human revision goes into `Wiki/Log.md` so there's a clear trail of who did what.

---

### 5. `wiki-plan` — Create or update a plan

**Trigger:** "plan for X", "let's plan", "add a plan", "update plan"

**Plan format:**
```markdown
# Plan: Title

> Status: **draft**

## Goal

What we're trying to achieve.

## Steps

- [ ] Step 1
- [x] Step 2 (completed)

## Decisions

Key choices made and why.

## History

| Date | Actor | Action |
|---|---|---|
| YYYY-MM-DD | LLM | Created plan |
| YYYY-MM-DD | Human | Revised: changed step 2 |
```

Plans follow the same revision workflow. History table tracks who did what.

---

### 6. `tour-start` — Start or resume a guided tour

**Trigger:** "start tour", "give me a tour", "continue tour", "where were we"

**What it does:**

1. Create `Tour/` locally if it doesn't exist (gitignored):
   ```
   Tour/
     Tour.md          plan + position + progress
     Sections/        one .md per section (narrative)
     Code/            one .wl per section (runnable code)
   ```

2. If no tour plan exists, generate one:
   - Read `Wiki/Index.md` and `Wiki/Status.md`
   - Order topics simplest → most complex
   - Write `Tour/Tour.md`

3. For each section, generate:
   - `Sections/NN_Name.md` — narrative: what it is, why it matters, key definitions, links to source files
   - `Code/NN_Name.wl` — self-contained Wolfram code for presentation/experimentation

4. Present summary to user, say:
   > "Here is section N: [Topic]. Narrative in `Tour/Sections/NN_Name.md`, code in `Tour/Code/NN_Name.wl`. Any feedback before we move on?"

5. **Wait for response.** Do not advance until user responds:
   - Approve → mark done, advance
   - Revise → update and re-present
   - Skip → mark skipped, advance
   - Stop → save position, end

**Tour.md format:**
```markdown
# Tour Plan

## Sections

1. [x] Topic A — summary  ← revised
2. [ ] Topic B — summary  ← current
3. [ ] Topic C — summary

## Position

Current section: 2
Last interaction: YYYY-MM-DD

## Log

| Date | Section | Action |
|---|---|---|
| YYYY-MM-DD | 1 | Presented, user approved |
```

Tour sections are code + narrative — the LLM waits for user feedback before advancing (this is the revision that matters).

---

### 7. `resource-add` — Add a resource to the wiki

**Trigger:** "add this paper", "save this resource", "note this repo", when encountering a new reference during work

**The resource pipeline:**

There are two layers — the **wiki article** (tracked in git, permanent) and the **local file** (gitignored, recoverable).

#### Step 1: Download (if applicable)

- Papers: download PDF to `Resources/` (local, gitignored)
- Repos: clone to `Resources/` or add as submodule
- Notebooks, datasets, tools: download to `Resources/`
- Web pages: no download needed, just the URL
- If `Resources/` doesn't exist, create it

#### Step 2: Summarize into wiki

Create `Wiki/Resources/Name.md`:

```markdown
# Author Year — Short Title

Full citation.

## Summary

What it is and why it matters. Key results or contents.

## Recover

Download: https://doi.org/...
```

or for repos:

```markdown
## Recover

Clone: git clone https://github.com/org/repo Resources/RepoName
```

or for tools/notebooks:

```markdown
## Recover

Download: https://...
Target: Resources/filename.nb
```

The `## Recover` section is machine-readable — the recovery script parses it.

#### Step 3: Update wiki

- Add one-line entry to `Wiki/Index.md` under Resources
- Add `[[backlinks]]` to related articles
- Append to `Wiki/Log.md`

#### Step 4: Recovery

`Resources/` is gitignored. To rebuild it from scratch:

1. Run `Scripts/recover_resources.sh` (or equivalent)
2. The script scans all `Wiki/Resources/*.md` files
3. For each file, it reads the `## Recover` section
4. Parses `Download:` lines → `curl`/`wget` to target path
5. Parses `Clone:` lines → `git clone`
6. Submodules are recovered separately via `git submodule update --init --recursive`

This means the wiki is the **single source of truth** for what resources exist and how to get them. The actual files are ephemeral.

**Resource article format — full example:**

```markdown
# Moore 1991 — Generalized Shifts

Cristopher Moore. *Generalized Shifts: Unpredictability and Undecidability
in Dynamical Systems.* Nonlinearity 4, 199-230, 1991.

## Summary

Introduces generalized shifts as a dynamical systems model equivalent to
Turing machines. Theorem 7: TM → GS (σ=1, τ=1). Theorem 8: GS → TM
(σ=1, τ=O(w)).

## Use in this project

Both theorems formalized in Lean. Theorem 7 fully proved. Theorem 8 has
1 sorry remaining.

## Recover

Download: https://doi.org/10.1088/0951-7715/4/2/002
Target: Resources/Moore_1991_GeneralizedShifts.pdf

## See also

- [[TMtoGS]], [[GStoTM]] — the formalizations
- [[GeneralizedShift]] — the system
```

**What counts as a resource:**
- Papers (PDFs)
- Git repos / submodules
- Notebooks (.nb, .ipynb)
- Datasets, spreadsheets
- Tools, packages, libraries
- Web pages, blog posts, documentation
- Emails, chat logs, slide decks (anything with useful content)

---

### 8. `notebook-create` — Create or update a presentation notebook

**Trigger:** "create notebook for X", "write a notebook", "add a notebook about Y", step 6 of "Adding a new universality proof"

**The notebook pipeline:**

Notebook sources are markdown files in `Wiki/Notebooks/`. They get converted to `.nb` files in `Notebooks/` (gitignored) and optionally published to Wolfram Cloud.

#### Step 1: Write the source

Create `Wiki/Notebooks/Name.md` — a structured markdown file that the Wolfram kernel converts to a notebook via `ImportString[md, {"Markdown", "Notebook"}]`. Structure:

```markdown
# Title

## Setup
<!-- Package loads, LeanLink init — becomes initialization cells -->

## Machine Definitions
<!-- Show Lean source, define WL objects -->

## Encoding
<!-- Encoding functions, examples -->

## Validation
<!-- Run machines, verify encodings on examples -->

## Lean Verification
<!-- LeanImportString, inspect theorems -->
```

Use fenced code blocks tagged `wolfram` for evaluatable Input cells. Plain text becomes Text cells. See the `create-notebook` skill for full markdown-to-cell mapping.

#### Step 2: Generate .nb

Run `Scripts/generate_notebooks.wls` — this reads all `Wiki/Notebooks/*.md` files, converts each to a `.nb` via the Wolfram kernel, and writes to `Notebooks/Name.nb`.

#### Step 3: Publish (optional)

Run `Scripts/publish_notebooks.wls` — uploads `.nb` files to Wolfram Cloud and prints the Cloud URLs.

#### Step 4: Register

- Add one-line entry to `Wiki/Index.md` under Notebooks
- Add a row to the Notebooks table in `README.md`:

```markdown
| Title | [Wiki/Notebooks/Name.md](Wiki/Notebooks/Name.md) | [Cloud](https://cloud-url) |
```

#### Naming convention

- Single edges: `Source_Target.md` (e.g. `TM_GS.md`)
- Chains: descriptive name (e.g. `CockeMinsky.md`)
- Exploration: topic name (e.g. `UniversalityGraph.md`)

---

## CLAUDE.md template (what the plugin adds to each repo)

The plugin should append this to the repo's CLAUDE.md:

```markdown
## Knowledge Base (Wiki)

Wiki/ is a plain-markdown knowledge base maintained by the LLM. Human-readable,
no special tooling needed.

### Maintenance rules

After every substantial step, the LLM:
1. Creates or updates relevant articles in Wiki/
2. Updates Wiki/Index.md
3. Updates Wiki/Status.md
4. Appends to Wiki/Log.md
5. Adds [[backlinks]] in See also sections

The wiki is documentation — the LLM keeps it accurate automatically.
No human sign-off needed for wiki prose.

### Human revision (code & functionality)

The LLM always presents new code, functionality, and plans to the user for
review. It does not silently overwrite user-edited content. The revision loop:
generate → present → wait for feedback → revise or proceed.

### Resources

Wiki/Resources/ holds summaries with download/clone URLs and a ## Recover
section. Resources/ (gitignored) holds actual binary files.

To rebuild all resources from wiki: Scripts/recover_resources.sh
The script parses ## Recover sections from Wiki/Resources/*.md.

### Notebooks

Wiki/Notebooks/ holds .md sources for Wolfram notebooks. Notebooks/ (gitignored)
holds generated .nb files. Scripts convert .md → .nb and optionally publish to
Wolfram Cloud. README.md lists all notebooks with source and cloud links.

### Guided Tour

Say "start tour" for an interactive walk through the project. Tour/ is
created on demand (local, gitignored). Each section produces a narrative .md
and runnable code file. The LLM stops after each section for feedback.
```

---

## Design principles

1. **Plain markdown only.** No databases, no embeddings, no special tooling. Works on GitHub, in Obsidian, in any text editor.

2. **LLM-navigable.** Index.md is the entry point. Folder structure is the taxonomy. ~100 articles / ~400k words fits in context via selective reading.

3. **Human-readable.** A person can browse the wiki without the LLM. Encyclopedia-style articles, not raw dumps.

4. **Revision matters for code and functionality, not wiki prose.** The LLM presents new code, features, and plans to the user and waits for feedback. Wiki articles are just documentation — the LLM maintains them automatically. User-edited content (plans, code, config) is protected from silent overwriting.

5. **Resources are recoverable.** Wiki/Resources/ is the source of truth (tracked). Resources/ holds ephemeral binary files (gitignored). A recovery script rebuilds Resources/ by parsing `## Recover` sections from wiki articles.

6. **On-demand local state.** Tour/ and Resources/ are created only when needed, gitignored. Wiki/ is tracked.

7. **Domain-agnostic.** The subfolder names under Wiki/ adapt to the project. The workflow (index, status, log, plans, resources, tour) is universal.

## History

| Date | Actor | Action |
|---|---|---|
| 2026-04-05 | LLM | Created plan from UniversalityDB workflow |
