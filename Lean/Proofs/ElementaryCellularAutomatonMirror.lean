/-
  ElementaryCellularAutomaton.Mirror

  Proof that ECA Rule 110 simulates ECA Rule 124 (and vice versa)
  via tape reversal. This is a bisimulation with σ = 1, τ = 1.

  Key theorem: rule110(a, b, c) = rule124(c, b, a) for all a, b, c ∈ {0,1}
-/

import Machines.ElementaryCellularAutomaton.Defs
import SimulationEncoding

namespace ElementaryCellularAutomaton

theorem mirrorProperty (a b c : Fin 2) :
    rule110 a b c = rule124 c b a := by
  revert a b c; decide

def reverseTape (n : Nat) (tape : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i => tape ⟨(n - 1 - i.val) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩

theorem reverseTapeInvolutive (n : Nat) (_hn : n ≥ 1) (tape : Fin n → Fin 2) :
    reverseTape n (reverseTape n tape) = tape := by
  funext i
  simp only [reverseTape]
  congr 1
  have hi := i.isLt
  refine Fin.ext ?_
  have h1 : (n - 1 - i.val) % n = n - 1 - i.val := Nat.mod_eq_of_lt (by omega)
  have h2 : n - 1 - (n - 1 - i.val) = i.val := by omega
  simp only [h1, h2, Nat.mod_eq_of_lt hi]

private theorem reverseRightIsLeft (n i : Nat) (hn : n ≥ 3) (hi : i < n) :
    (n - 1 - ((i + 1) % n)) % n = ((n - 1 - i) % n + n - 1) % n := by
  have h1 : (n - 1 - i) % n = n - 1 - i := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  by_cases h : i < n - 1
  · rw [Nat.mod_eq_of_lt (by omega : i + 1 < n)]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 - (i + 1) < n)]
    have : n - 1 - i + n - 1 = (n - 2 - i) + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hi2 : i = n - 1 := by omega
    subst hi2
    rw [show n - 1 + 1 = n from by omega, Nat.mod_self]
    simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]

private theorem reverseLeftIsRight (n i : Nat) (hn : n ≥ 3) (hi : i < n) :
    (n - 1 - ((i + n - 1) % n)) % n = ((n - 1 - i) % n + 1) % n := by
  have h1 : (n - 1 - i) % n = n - 1 - i := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  by_cases h : i > 0
  · have h2 : i + n - 1 = (i - 1) + n := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < n)]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 - (i - 1) < n)]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 - i + 1 < n)]
    omega
  · have hi2 : i = 0 := by omega
    subst hi2
    simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    rw [show n - 1 + 1 = n from by omega, Nat.mod_self]

theorem mirrorSimulationGeneral (n : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    step rule110 n (reverseTape n tape) = reverseTape n (step rule124 n tape) := by
  funext i
  simp only [step, reverseTape]
  rw [mirrorProperty]
  have hi := i.isLt
  congr 1
  · congr 1; exact Fin.ext (reverseRightIsLeft n i.val hn hi)
  · congr 1; exact Fin.ext (reverseLeftIsRight n i.val hn hi)

theorem mirrorSimulationSteps (n k : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    iterate rule110 n (reverseTape n tape) k =
    reverseTape n (iterate rule124 n tape k) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    simp [iterate]
    rw [ih]
    exact mirrorSimulationGeneral n hn (iterate rule124 n tape k)

-- ============================================================================
-- Simulation instance: Rule 110 ↔ Rule 124 via tape reversal
-- ============================================================================

theorem rule110CommutesRule124 (n : Nat) (hn : n ≥ 3)
    (config config' : Fin n → Fin 2)
    (h : step rule124 n config = config') :
    ∃ m, (toComputationalMachine rule110 n).iterationStep m
      (reverseTape n config) = some (reverseTape n config') :=
  ⟨1, by simp [ComputationalMachine.iterationStep, toComputationalMachine,
               mirrorSimulationGeneral n hn config, h]⟩

theorem rule124CommutesRule110 (n : Nat) (hn : n ≥ 3)
    (config config' : Fin n → Fin 2)
    (h : step rule110 n config = config') :
    ∃ m, (toComputationalMachine rule124 n).iterationStep m
      (reverseTape n config) = some (reverseTape n config') := by
  have hmirror : step rule124 n (reverseTape n config) =
      reverseTape n (step rule110 n config) := by
    have h1 := mirrorSimulationGeneral n hn (reverseTape n config)
    rw [reverseTapeInvolutive n (by omega) config] at h1
    have h2 := congrArg (reverseTape n) h1
    simp [reverseTapeInvolutive n (by omega)] at h2
    exact h2.symm
  exact ⟨1, by simp [ComputationalMachine.iterationStep, toComputationalMachine, hmirror, h]⟩

/-- ECA never halts (step is total), so the halting condition is vacuously true. -/
theorem ecaStepNeverNone (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) (n : Nat)
    (config : Fin n → Fin 2) :
    (toComputationalMachine rule n).step config ≠ none := by
  simp [toComputationalMachine]

/-- Rule 110 simulates Rule 124 via tape reversal. -/
def rule110SimulatesRule124 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule110 n)
      (toComputationalMachine rule124 n) where
  encode := reverseTape n
  commutes config config' h := rule110CommutesRule124 n hn config config' (by simpa [toComputationalMachine] using h)
  halting config h := absurd h (ecaStepNeverNone rule124 n config)

/-- Rule 124 simulates Rule 110 via tape reversal. -/
def rule124SimulatesRule110 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule124 n)
      (toComputationalMachine rule110 n) where
  encode := reverseTape n
  commutes config config' h := rule124CommutesRule110 n hn config config' (by simpa [toComputationalMachine] using h)
  halting config h := absurd h (ecaStepNeverNone rule110 n config)

end ElementaryCellularAutomaton
