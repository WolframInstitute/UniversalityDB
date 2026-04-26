/-
  ComputationalMachine

  A computational machine is a type of configurations with a partial step function.
  This is the base abstraction for all machine types in the Universality Graph.

  Every concrete system (TuringMachine, GeneralizedShift, ElementaryCellularAutomaton,
  TagSystem, CyclicTagSystem) can be wrapped as a ComputationalMachine, enabling
  type-erased edge registration.
-/

structure ComputationalMachine where
  Configuration : Type
  step : Configuration → Option Configuration

namespace ComputationalMachine

def iterationStep (machine : ComputationalMachine) : Nat → machine.Configuration → Option machine.Configuration
  | 0, config => some config
  | n + 1, config => machine.step config >>= iterationStep machine n

def Halts (machine : ComputationalMachine) (config : machine.Configuration) : Prop :=
  ∃ n, machine.iterationStep n config = none

theorem iterationStep_zero (machine : ComputationalMachine) (config : machine.Configuration) :
    machine.iterationStep 0 config = some config := rfl

theorem iterationStep_succ (machine : ComputationalMachine) (n : Nat) (config config' : machine.Configuration) :
    machine.step config = some config' →
    machine.iterationStep (n + 1) config = machine.iterationStep n config' := by
  intro h; simp [iterationStep, h]

theorem iterationStep_succ_none (machine : ComputationalMachine) (n : Nat) (config : machine.Configuration) :
    machine.step config = none →
    machine.iterationStep (n + 1) config = none := by
  intro h; simp [iterationStep, h]

theorem iterationStep_add (machine : ComputationalMachine) (m n : Nat) (config : machine.Configuration) :
    machine.iterationStep (m + n) config = (machine.iterationStep m config).bind (machine.iterationStep n) := by
  induction m generalizing config with
  | zero => simp [iterationStep]
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h]
    simp only [iterationStep]
    cases machine.step config with
    | none => rfl
    | some config' => exact ih config'

theorem Halts_of_step_none {machine : ComputationalMachine} {config : machine.Configuration}
    (h : machine.step config = none) : machine.Halts config :=
  ⟨1, by simp [iterationStep, h]⟩

end ComputationalMachine
