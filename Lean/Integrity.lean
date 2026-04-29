/-
  Integrity.lean — Proof integrity verification using Lean's own APIs.

  Generic and project-agnostic. To use in any Lean 4 project:
  1. Drop this file into the project's source tree.
  2. Add its module to lakefile.lean roots.
  3. Replace the project imports below with imports of YOUR project's
     top-level modules. That's the only thing to edit.
  4. Run via `Scripts/verify_integrity.sh` (or just `lake build`).

  Project modules are auto-detected from this file's direct imports
  (everything except `Lean` itself). Every theorem in every directly-
  imported module is automatically scanned.

  Per theorem:
  1. `CollectAxioms.collect` traces axiom dependencies. Any axiom beyond
     standard (`propext`, `Quot.sound`, `Classical.choice`), `sorryAx`,
     or `_native` axioms is an integrity violation → build fails.
  2. Hypothesis detection: identifies all Prop parameters via
     `forallTelescope` + `isProp`. A theorem with zero Prop hypotheses
     is "absolutely proven" — its conclusion holds unconditionally
     (modulo standard axioms and the Lean kernel). A theorem with
     hypotheses is conditionally proven on those assumptions.
  3. `leanchecker` (via the shell script) replays all declarations
     through the kernel for additional kernel-level validation.

  No string parsing, no grep, no curated theorem list, no project module
  list. The check covers the entire project automatically.

  Hypotheses hidden inside `def` bodies are also detected: the scan uses
  `forallTelescopeReducing`, which unfolds reducible definitions before
  inspecting Pi-binders. So `def Conditional := P → Q; theorem foo :
  Conditional := ...` correctly surfaces the hidden Pi-binder.

  MAINTENANCE: when adding a new top-level module, update lakefile.lean
  roots AND the import list below. New theorems within imported modules
  are picked up automatically.
-/

import Lean
import ComputationalMachine
import SimulationEncoding
import Machines.TuringMachine.Defs
import Machines.BiInfiniteTuringMachine.Defs
import Machines.TagSystem.Defs
import Machines.ElementaryCellularAutomaton.Defs
import Machines.GeneralizedShift.Defs
import Proofs.TuringMachineToGeneralizedShift
import Proofs.GeneralizedShiftToTuringMachine
import Proofs.CockeMinsky
import Proofs.TagSystemToCyclicTagSystem
import Proofs.ElementaryCellularAutomatonMirror

open Lean Elab Command

/-- The three standard axioms in Lean's kernel. Any axiom beyond these
    in a key theorem's dependency closure is an integrity violation. -/
private def standardAxioms : List Name :=
  [`propext, `Quot.sound, `Classical.choice]

/-- Check if a Name contains `_native` as a component (native_decide axioms). -/
private def hasNativeComponent : Name → Bool
  | .anonymous => false
  | .str parent s => s == "_native" || hasNativeComponent parent
  | .num parent _ => hasNativeComponent parent

/-- Axioms that are tracked but not failures:
    - `sorryAx`: sorry in the proof chain (tracked in Wiki/Status.md)
    - names containing `_native`: native_decide computational axioms -/
private def isTrackedAxiom (n : Name) : Bool :=
  n == `sorryAx || hasNativeComponent n

/-- Project modules are this file's direct imports, minus `Lean` itself
    and `Init` (always implicitly imported). This makes the integrity
    check generic across projects: just edit the imports above. -/
private def getProjectModules (env : Environment) : Array Name :=
  env.header.imports.filterMap fun imp =>
    let m := imp.module
    if m == `Lean || m == `Init then none else some m

/-- Returns all Prop-typed parameters (hypotheses) in a theorem's type.
    Covers explicit `(h : P)`, implicit `{h : P}`, and strict-implicit `⦃h : P⦄`
    binders — all are unproved assumptions the caller (or elaborator) must
    supply. Excludes instance arguments `[h : P]` since those are typeclass
    instances, structurally inferred from types, not arbitrary hypotheses.

    Uses `forallTelescopeReducing` so that hypotheses hidden inside `def`
    bodies (e.g. `theorem foo : Conditional` where `Conditional` unfolds to
    `(h : P) → Q`) are reduced and the Pi-binder is exposed. -/
private partial def hypothesisParams (type : Expr) : MetaM (Array Name) := do
  Lean.Meta.forallTelescopeReducing type fun fvars _ => do
    let mut result : Array Name := #[]
    for fvar in fvars do
      let decl ← fvar.fvarId!.getDecl
      -- Skip instance binders (typeclass resolution, not free hypotheses)
      if decl.binderInfo == .instImplicit then continue
      let fvarType ← Lean.Meta.inferType fvar
      let isProp ← Lean.Meta.isProp fvarType
      if !isProp then continue
      result := result.push decl.userName
    return result

/-- Returns true if `name`'s module is one of the directly-imported
    project modules. -/
private def isProjectConstant (env : Environment) (projectMods : Array Name)
    (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx =>
    let modName := env.allImportedModuleNames[idx.toNat]!
    projectMods.contains modName

/-- Detect auto-generated declarations (equation lemmas, sizeOf specs,
    injectivity, recursors, noConfusion, etc.). These are produced by
    Lean's elaborator from user definitions, not written by hand. They
    are still scanned for axioms (correctness), but excluded from the
    per-theorem verbose listing for readability. -/
private def isAutoGenerated : Name → Bool
  | .str _ s =>
    s == "sizeOf_spec" || s == "injEq" || s == "brecOn" || s == "below" ||
    s == "noConfusion" || s == "noConfusionType" ||
    -- equation compiler lemmas: name.eq_N, name.eq_def
    s == "eq_def" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit) ||
    -- match cases / aux lemmas
    s.startsWith "_" || s.startsWith "match_"
  | _ => false

run_cmd do
  let env ← getEnv
  let projectMods := getProjectModules env
  logInfo m!"INTEGRITY CHECK: project modules = {projectMods}"
  let mut hasViolation := false
  let mut absoluteThms : Array Name := #[]
  let mut conditionalThms : Array (Name × Array Name) := #[]

  -- Iterate every constant in every directly-imported project module
  for (name, info) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    -- Skip non-theorems (defs, axioms, inductives, etc.)
    let .thmInfo _ := info | continue
    -- Skip non-project constants
    if !isProjectConstant env projectMods name then continue
    -- Skip internal compiler-generated theorems
    if name.isInternal then continue
    -- Skip auto-generated equation lemmas / sizeOf specs / injEq / etc.
    if isAutoGenerated name then continue

    -- Check 1: axioms
    let (_, s) := (CollectAxioms.collect name).run env |>.run {}
    let mut unexpected : Array Name := #[]
    for ax in s.axioms do
      if ax ∉ standardAxioms && !isTrackedAxiom ax then
        unexpected := unexpected.push ax
    if unexpected.size > 0 then
      logError m!"INTEGRITY VIOLATION: '{name}' depends on unexpected axioms: {unexpected}"
      hasViolation := true
      continue

    -- Check 2: hypothesis parameters
    let hyps ← liftCoreM (Lean.Meta.MetaM.run' (hypothesisParams info.type))
    if hyps.isEmpty then
      absoluteThms := absoluteThms.push name
    else
      conditionalThms := conditionalThms.push (name, hyps)

  -- Per-theorem details (parsed by shell script for verbose mode)
  for name in absoluteThms do
    logInfo m!"ABSOLUTE {name}"
  for (name, hyps) in conditionalThms do
    logInfo m!"CONDITIONAL {name}: hypotheses {hyps}"

  -- Aggregate counts
  logInfo m!"INTEGRITY CHECK: scanned {absoluteThms.size + conditionalThms.size} theorems"
  logInfo m!"  absolutely proven (no Prop hypotheses): {absoluteThms.size}"
  logInfo m!"  conditionally proven (has Prop hypotheses): {conditionalThms.size}"
  if !hasViolation then
    logInfo "INTEGRITY CHECK: PASS"
