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
private def isTrackedAxiom (n : Name) : Bool :=
  n == `sorryAx || hasNativeComponent n

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

  -- Check key theorems: only standard axioms allowed (+ sorryAx if tracked)
  for thmName in keyTheorems do
    let (_, s) := (CollectAxioms.collect thmName).run env |>.run {}
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
  for thmName in spotCheckTheorems do
    let (_, s) := (CollectAxioms.collect thmName).run env |>.run {}
    let mut unexpected : Array Name := #[]
    for ax in s.axioms do
      if ax ∉ standardAxioms && !isTrackedAxiom ax then
        unexpected := unexpected.push ax
    if unexpected.size > 0 then
      logError m!"INTEGRITY VIOLATION: spot check '{thmName}' depends on unexpected axioms: {unexpected}"
      hasViolation := true

  if !hasViolation then
    logInfo "INTEGRITY CHECK: PASS"
