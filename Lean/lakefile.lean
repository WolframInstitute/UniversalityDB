import Lake
open Lake DSL

package «UniversalityDB» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «UniversalityDB» where
  srcDir := "."
  roots := #[
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
    `Proofs.ElementaryCellularAutomatonMirror,
    `Proofs.ElementaryCellularAutomatonConjugation,
    `Proofs.TMtoGS,
    `Edges,
    `EdgeAudit,
    `Integrity
  ]
