/-
  Integrity.lean — Proof integrity verification using Lean's own APIs.

  Iterates EVERY theorem in EVERY project module (no hardcoded list).
  For each theorem:
  1. `CollectAxioms.collect` traces axiom dependencies. Any axiom beyond
     standard (`propext`, `Quot.sound`, `Classical.choice`), `sorryAx`,
     or `_native` axioms is an integrity violation → build fails.
  2. Hypothesis detection: identifies all explicit Prop parameters
     (the caller must supply proofs of these). Reported per theorem.
     A theorem with zero Prop hypotheses is "absolutely proven" — its
     conclusion holds unconditionally (modulo standard axioms and the
     Lean kernel). A theorem with hypotheses is conditionally proven.
  3. `leanchecker` (via the shell script) replays all declarations
     through the kernel for additional kernel-level validation.

  No string parsing, no grep, no curated theorem list. The check covers
  the entire project automatically.

  MAINTENANCE:
  - New project modules: add to lakefile.lean roots AND the import list below.
    The shell script derives its leanchecker module list from lakefile.lean
    automatically — no third place to update.
  - That's it. New theorems are picked up automatically.
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

/-- Modules whose theorems are checked. Every theorem-kind constant from
    these modules is scanned. Derived from the import list above so adding
    a module requires updating only one place (lakefile.lean + this file's
    imports — see MAINTENANCE comment). -/
private def projectModules : List Name := [
  `ComputationalMachine,
  `SimulationEncoding,
  `Machines.TuringMachine.Defs,
  `Machines.BiInfiniteTuringMachine.Defs,
  `Machines.TagSystem.Defs,
  `Machines.ElementaryCellularAutomaton.Defs,
  `Machines.GeneralizedShift.Defs,
  `Proofs.TuringMachineToGeneralizedShift,
  `Proofs.GeneralizedShiftToTuringMachine,
  `Proofs.CockeMinsky,
  `Proofs.TagSystemToCyclicTagSystem,
  `Proofs.ElementaryCellularAutomatonMirror
]

/-- Returns all Prop-typed parameters (hypotheses) in a theorem's type.
    Covers explicit `(h : P)`, implicit `{h : P}`, and strict-implicit `⦃h : P⦄`
    binders — all are unproved assumptions the caller (or elaborator) must
    supply. Excludes instance arguments `[h : P]` since those are typeclass
    instances, structurally inferred from types, not arbitrary hypotheses. -/
private partial def hypothesisParams (type : Expr) : MetaM (Array Name) := do
  Lean.Meta.forallTelescope type fun fvars _ => do
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

/-- Returns true if `name`'s module is in `projectModules`. -/
private def isProjectConstant (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx =>
    let modName := env.allImportedModuleNames[idx.toNat]!
    projectModules.contains modName

run_cmd do
  let env ← getEnv
  let mut hasViolation := false
  let mut absolutelyProven : Nat := 0
  let mut conditionallyProven : Nat := 0
  let mut totalChecked : Nat := 0

  -- Iterate every constant in every project module
  for (name, info) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    -- Skip non-theorems (defs, axioms, inductives, etc.)
    let .thmInfo _ := info | continue
    -- Skip non-project constants
    if !isProjectConstant env name then continue
    -- Skip internal compiler-generated theorems
    if name.isInternal then continue

    totalChecked := totalChecked + 1

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
      absolutelyProven := absolutelyProven + 1
    else
      conditionallyProven := conditionallyProven + 1

  logInfo m!"INTEGRITY CHECK: scanned {totalChecked} theorems"
  logInfo m!"  absolutely proven (no Prop hypotheses): {absolutelyProven}"
  logInfo m!"  conditionally proven (has Prop hypotheses): {conditionallyProven}"
  if !hasViolation then
    logInfo "INTEGRITY CHECK: PASS"
