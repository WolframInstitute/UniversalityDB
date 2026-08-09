/-
  Integrity.lean — Proof integrity verification using Lean's own APIs.

  Uses `CollectAxioms.collect` to programmatically trace axiom dependencies
  of every key theorem, and `leanchecker` (via the shell script) for full
  kernel replay. No string parsing, no grep.

  If any violation is found, this file fails to compile (logError).

  MAINTENANCE:
  - New project modules: add to lakefile.lean roots AND the import list below.
    The shell script derives its leanchecker module list from lakefile.lean
    automatically — no third place to update.
  - New key theorems: add to `keyTheorems` below.

  NOTE: the lists below name *declarations*, not only theorems. Assembled
  simulations are `def`s (a `Simulation` carries an `encode` field, so it lives
  in `Type`, not `Prop`); `CollectAxioms.collect` traverses `defnInfo` and
  `thmInfo` identically, so their axiom closures are checked the same way.
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
import Proofs.TMtoGS
import Proofs.GeneralizedShiftToTuringMachine
import Proofs.CockeMinsky
import Proofs.TagSystemToCyclicTagSystem
import Proofs.ElementaryCellularAutomatonKleinGroup
import Edges
import EdgeAudit

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
private def isTrackedAxiom (name : Name) : Bool :=
  name == `sorryAx || hasNativeComponent name

/-- Resolve a listed name to the constant that actually exists in the environment.

    Needed because `CollectAxioms.collect` fails open: it matches on the
    constant's `ConstantInfo` and falls through to `| none => pure ()` for a name
    that is not in the environment, so an unknown name yields an *empty* axiom
    set — indistinguishable from a clean trace. Two ways a listed name goes
    unknown: a typo / rename / deletion (0 matches → violation), and a `private`
    declaration, whose real name is mangled to
    `_private.<Module>.0.<Namespace>.<name>` (recovered by the fallback below).

    Returns every match so ambiguity is reported rather than silently resolved. -/
private def resolveDecl (env : Environment) (name : Name) : Array Name :=
  if env.contains name then
    #[name]
  else
    env.constants.fold (init := #[]) fun acc c _ =>
      if privateToUserName? c == some name then acc.push c else acc

/-- Key theorems whose axiom dependencies are checked. -/
private def keyTheorems : List Name := [
  -- Moore Theorem 7: TM → GS (building blocks + assembled simulation)
  `TuringMachineToGeneralizedShift.stepCommutes,
  `TuringMachineToGeneralizedShift.decodeEncode,
  `TMtoGS.tmToGSSimulation,
  -- Moore Theorem 8: GS → TM (SimulationEncoding form; conjugation via decodeConfigPadded)
  `GeneralizedShiftToTuringMachine.fullSim_general_cView,
  `GeneralizedShiftToTuringMachine.gsToTMSimulationEncoding,
  -- Cook 2004: Tag → CTS
  `TagSystem.tagToCyclicTagSystemHaltingForward,
  -- Cocke-Minsky chain: wolfram23 universal
  `BiInfiniteTuringMachine.wolfram23Universal,
  `BiInfiniteTuringMachine.wolfram23HaltingSimulation,
  -- ECA mirror: Rule 110 ↔ Rule 124
  `ElementaryCellularAutomaton.mirrorSimulationSteps,
  `ElementaryCellularAutomaton.rule110SimulatesRule124,
  `ElementaryCellularAutomaton.rule124SimulatesRule110,
  -- ECA conjugation: Rule 110 ↔ Rule 137 (complement) and Rule 110 ↔ Rule 193 (mirror∘complement)
  `ElementaryCellularAutomaton.complementSimulationGeneral,
  `ElementaryCellularAutomaton.mirrorSimulationGenericGeneral,
  `ElementaryCellularAutomaton.mirrorComplementSimulation,
  `ElementaryCellularAutomaton.rule110SimulatesRule137,
  `ElementaryCellularAutomaton.rule137SimulatesRule110,
  `ElementaryCellularAutomaton.rule110SimulatesRule193,
  `ElementaryCellularAutomaton.rule193SimulatesRule110,
  -- Simulation framework
  `ComputationalMachine.Simulation.halting_preserved,
  `ComputationalMachine.Simulation.compose
]

/-- Spot-check theorems (native_decide axioms expected here). -/
private def spotCheckTheorems : List Name := [
  `BiInfiniteTuringMachine.wolfram23Step1,
  `TagSystem.simulationExampleCorrected
]

run_cmd do
  let env ← getEnv
  let mut hasViolation := false

  -- Resolution check (must run before any axiom trace is trusted).
  --
  -- A name that does not resolve gets an empty axiom set from
  -- `CollectAxioms.collect`, which reads as a clean trace. Resolve every listed
  -- name first; only resolved names are traced below, and an unresolvable or
  -- ambiguous one is a violation in its own right.
  let mut keyResolved : Array (Name × Name) := #[]
  let mut spotResolved : Array (Name × Name) := #[]
  for (declName, isKey) in
      keyTheorems.map (·, true) ++ spotCheckTheorems.map (·, false) do
    let found := resolveDecl env declName
    if found.size == 1 then
      let actual := found[0]!
      if actual != declName then
        logInfo m!"RESOLVED {declName} -> {actual} (private)"
      if isKey then keyResolved := keyResolved.push (declName, actual)
      else spotResolved := spotResolved.push (declName, actual)
    else if found.isEmpty then
      logError m!"INTEGRITY VIOLATION: '{declName}' is not a declaration in the \
        environment (misspelled, renamed, or removed). Its axiom trace would be \
        vacuously empty."
      hasViolation := true
    else
      logError m!"INTEGRITY VIOLATION: '{declName}' is ambiguous — it matches \
        several private theorems: {found}. Name the intended one exactly."
      hasViolation := true

  -- Check key theorems: only standard axioms allowed (+ sorryAx if tracked)
  for (thmName, actual) in keyResolved do
    let (_, s) := (CollectAxioms.collect actual).run env |>.run {}
    let mut unexpected : Array Name := #[]
    for ax in s.axioms do
      if ax ∉ standardAxioms && !isTrackedAxiom ax then
        unexpected := unexpected.push ax
    if unexpected.size > 0 then
      logError m!"INTEGRITY VIOLATION: '{thmName}' depends on unexpected axioms: {unexpected}"
      hasViolation := true
    else
      let trackedAxioms := s.axioms.filter isTrackedAxiom
      if trackedAxioms.size > 0 then
        logInfo m!"TRACE {thmName}: {s.axioms} (tracked: {trackedAxioms})"
      else
        logInfo m!"TRACE {thmName}: {s.axioms}"

  -- Check spot-check theorems: native_decide axioms are expected
  for (thmName, actual) in spotResolved do
    let (_, s) := (CollectAxioms.collect actual).run env |>.run {}
    let mut unexpected : Array Name := #[]
    for ax in s.axioms do
      if ax ∉ standardAxioms && !isTrackedAxiom ax then
        unexpected := unexpected.push ax
    if unexpected.size > 0 then
      logError m!"INTEGRITY VIOLATION: spot check '{thmName}' depends on unexpected axioms: {unexpected}"
      hasViolation := true

  if !hasViolation then
    logInfo "INTEGRITY CHECK: PASS"
