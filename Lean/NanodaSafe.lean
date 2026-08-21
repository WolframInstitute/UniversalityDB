/-
A standalone module, containing modules to be check by Nanoda (not part of `lake build`).
(Nanoda cannot verify native_decide-dependent proofs)

Please add here modules with no `native_decide` anywhere in its transitive closure.

Covered keyTheorems (12 of 20) — imported via Proofs.ElementaryCellularAutomatonKleinGroup,
which alone transitively pulls in ComputationalMachine, SimulationEncoding, and
Machines.ElementaryCellularAutomaton.Defs:
  ElementaryCellularAutomaton.mirrorSimulationSteps
  ElementaryCellularAutomaton.rule110SimulatesRule124 / rule124SimulatesRule110
  ElementaryCellularAutomaton.complementSimulationGeneral
  ElementaryCellularAutomaton.mirrorSimulationGenericGeneral
  ElementaryCellularAutomaton.mirrorComplementSimulation
  ElementaryCellularAutomaton.rule110SimulatesRule137 / rule137SimulatesRule110
  ElementaryCellularAutomaton.rule110SimulatesRule193 / rule193SimulatesRule110
  ComputationalMachine.Simulation.halting_preserved / .compose

NOT covered (8 of 20) — depend on Machines.BiInfiniteTuringMachine.Defs and/or
Machines.TagSystem.Defs, both of which use native_decide directly:
  TuringMachineToGeneralizedShift.stepCommutes / decodeEncode
  TMtoGS.tmToGSSimulation
  GeneralizedShiftToTuringMachine.fullSim_general_cView / gsToTMSimulationEncoding
  TagSystem.tagToCyclicTagSystemHaltingForward
  BiInfiniteTuringMachine.wolfram23Universal / wolfram23HaltingSimulation

When adding a new entry to `keyTheorems`, add its module here too if its transitive
closure has no native_decide.
-/
import Proofs.ElementaryCellularAutomatonKleinGroup
