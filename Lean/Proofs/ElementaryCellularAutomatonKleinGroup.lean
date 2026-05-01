/-
  ElementaryCellularAutomaton.KleinGroup

  Klein-4 group of ECA rule conjugations. Two trivial symmetries:

  - Mirror     f(a,b,c) = g(c,b,a)        ↔  tape reversal
  - Complement f(a,b,c) = ¬g(¬a,¬b,¬c)    ↔  bit complement

  They commute and are involutive, so the four rules
    {rule, mirror rule, complement rule, mirror (complement rule)}
  form a Klein-4 orbit.

  For Rule 110 the orbit is {110, 124, 137, 193}.

  This file contains the full ECA Klein-group proof slice:
  - generic mirror simulation via tape reversal,
  - generic complement simulation via bit complement,
  - the composed mirror ∘ complement simulation,
  - the specializations 110 ↔ 124, 110 ↔ 137, 110 ↔ 193.
-/

import Machines.ElementaryCellularAutomaton.Defs
import SimulationEncoding

namespace ElementaryCellularAutomaton

/-! ## Bit complement on `Fin 2` -/

def flip2 : Fin 2 → Fin 2 :=
  fun b => ⟨1 - b.val, by have := b.isLt; omega⟩

@[simp] theorem flip2_flip2 (b : Fin 2) : flip2 (flip2 b) = b := by
  revert b; decide

/-! ## Conjugated rules -/

def mirrorRule (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) :
    Fin 2 → Fin 2 → Fin 2 → Fin 2 :=
  fun a b c => rule c b a

def complementRule (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) :
    Fin 2 → Fin 2 → Fin 2 → Fin 2 :=
  fun a b c => flip2 (rule (flip2 a) (flip2 b) (flip2 c))

theorem mirrorRule_involutive (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) :
    mirrorRule (mirrorRule rule) = rule := rfl

theorem complementRule_involutive (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) :
    complementRule (complementRule rule) = rule := by
  funext a b c; simp [complementRule]

theorem mirror_complement_comm (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) :
    mirrorRule (complementRule rule) = complementRule (mirrorRule rule) := rfl

/-! ## Tape transforms -/

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

theorem reverseRightIsLeft (n i : Nat) (hn : n ≥ 3) (hi : i < n) :
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

theorem reverseLeftIsRight (n i : Nat) (hn : n ≥ 3) (hi : i < n) :
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

def complementTape (n : Nat) (tape : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i => flip2 (tape i)

theorem complementTapeInvolutive (n : Nat) (tape : Fin n → Fin 2) :
    complementTape n (complementTape n tape) = tape := by
  funext i; simp [complementTape]

theorem reverseTape_complementTape_comm (n : Nat) (tape : Fin n → Fin 2) :
    reverseTape n (complementTape n tape) = complementTape n (reverseTape n tape) := by
  funext i; simp [reverseTape, complementTape]

/-! ## Specific Rule 110 orbit identifications -/

theorem mirrorRule_rule110 : mirrorRule rule110 = rule124 := by
  funext a b c; revert a b c; decide

theorem complementRule_rule110 : complementRule rule110 = rule137 := by
  funext a b c; revert a b c; decide

theorem mirrorRule_rule137 : mirrorRule rule137 = rule193 := by
  funext a b c; revert a b c; decide

theorem complementRule_rule124 : complementRule rule124 = rule193 := by
  funext a b c; revert a b c; decide

theorem complementRule_rule137 : complementRule rule137 = rule110 := by
  have h := complementRule_involutive rule110
  rw [complementRule_rule110] at h
  exact h

theorem mirrorRule_rule124 : mirrorRule rule124 = rule110 := by
  have h := mirrorRule_involutive rule110
  rw [mirrorRule_rule110] at h
  exact h

theorem complementRule_rule193 : complementRule rule193 = rule124 := by
  have h := complementRule_involutive rule124
  rw [complementRule_rule124] at h
  exact h

theorem mirrorRule_rule193 : mirrorRule rule193 = rule137 := by
  have h := mirrorRule_involutive rule137
  rw [mirrorRule_rule137] at h
  exact h

/-! ## Generic conjugation lemmas -/

theorem mirrorSimulationGenericGeneral
    (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    step (mirrorRule rule) n (reverseTape n tape) =
    reverseTape n (step rule n tape) := by
  funext i
  simp only [step, reverseTape, mirrorRule]
  have hi := i.isLt
  congr 1
  · congr 1
    exact Fin.ext (reverseRightIsLeft n i.val hn hi)
  · congr 1
    exact Fin.ext (reverseLeftIsRight n i.val hn hi)

theorem mirrorSimulationGenericSteps
    (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n k : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    iterate (mirrorRule rule) n (reverseTape n tape) k =
    reverseTape n (iterate rule n tape k) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    simp [iterate]
    rw [ih]
    exact mirrorSimulationGenericGeneral rule n hn (iterate rule n tape k)

theorem complementSimulationGeneral (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n : Nat) (tape : Fin n → Fin 2) :
    step (complementRule rule) n (complementTape n tape) =
    complementTape n (step rule n tape) := by
  funext i
  simp [step, complementTape, complementRule]

/-! ## Specialized mirror statements for Rule 110 ↔ Rule 124 -/

theorem mirrorProperty (a b c : Fin 2) :
    rule110 a b c = rule124 c b a := by
  revert a b c; decide

theorem mirrorSimulationGeneral (n : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    step rule110 n (reverseTape n tape) = reverseTape n (step rule124 n tape) := by
  simpa [mirrorRule_rule124] using mirrorSimulationGenericGeneral rule124 n hn tape

theorem mirrorSimulationSteps (n k : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    iterate rule110 n (reverseTape n tape) k =
    reverseTape n (iterate rule124 n tape k) := by
  simpa [mirrorRule_rule124] using mirrorSimulationGenericSteps rule124 n k hn tape

/-! ## Composed transform: reverse ∘ complement -/

def mirrorComplementTape (n : Nat) (tape : Fin n → Fin 2) : Fin n → Fin 2 :=
  reverseTape n (complementTape n tape)

theorem mirrorComplementTapeInvolutive (n : Nat) (hn : n ≥ 1) (tape : Fin n → Fin 2) :
    mirrorComplementTape n (mirrorComplementTape n tape) = tape := by
  unfold mirrorComplementTape
  rw [reverseTape_complementTape_comm n (reverseTape n (complementTape n tape))]
  rw [reverseTapeInvolutive n hn (complementTape n tape)]
  exact complementTapeInvolutive n tape

theorem mirrorComplementSimulation (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    step (mirrorRule (complementRule rule)) n (mirrorComplementTape n tape) =
    mirrorComplementTape n (step rule n tape) := by
  unfold mirrorComplementTape
  rw [mirrorSimulationGenericGeneral (complementRule rule) n hn (complementTape n tape)]
  rw [complementSimulationGeneral rule n tape]

/-! ## Generic `Simulation` wrappers -/

private theorem stepNeverNone (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) (n : Nat)
    (config : Fin n → Fin 2) :
    (toComputationalMachine rule n).step config ≠ none := by
  simp [toComputationalMachine]

def mirrorRuleSimulatesRule
    (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine (mirrorRule rule) n)
      (toComputationalMachine rule n) where
  encode := reverseTape n
  commutes := fun config config' h => by
    have hStep : step rule n config = config' := by
      simpa [toComputationalMachine] using h
    refine ⟨1, ?_⟩
    simp [ComputationalMachine.iterationStep, toComputationalMachine,
      mirrorSimulationGenericGeneral rule n hn config, hStep]
  halting config h := absurd h (stepNeverNone rule n config)

def ruleSimulatesMirrorRule
    (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule n)
      (toComputationalMachine (mirrorRule rule) n) where
  encode := reverseTape n
  commutes := fun config config' h => by
    have hStep : step (mirrorRule rule) n config = config' := by
      simpa [toComputationalMachine] using h
    have hmirror : step rule n (reverseTape n config) =
        reverseTape n (step (mirrorRule rule) n config) := by
      have h1 := mirrorSimulationGenericGeneral rule n hn (reverseTape n config)
      rw [reverseTapeInvolutive n (by omega) config] at h1
      have h2 := congrArg (reverseTape n) h1
      simp [reverseTapeInvolutive n (by omega)] at h2
      exact h2.symm
    refine ⟨1, ?_⟩
    simp [ComputationalMachine.iterationStep, toComputationalMachine, hmirror, hStep]
  halting config h := absurd h (stepNeverNone (mirrorRule rule) n config)

/-! ## Rule 110 orbit wrappers -/

def rule110SimulatesRule124 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule110 n)
      (toComputationalMachine rule124 n) := by
  simpa [mirrorRule_rule110] using ruleSimulatesMirrorRule rule110 n hn

def rule124SimulatesRule110 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule124 n)
      (toComputationalMachine rule110 n) := by
  simpa [mirrorRule_rule124] using ruleSimulatesMirrorRule rule124 n hn

def rule110SimulatesRule137 (n : Nat) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule110 n)
      (toComputationalMachine rule137 n) where
  encode := complementTape n
  commutes := fun config config' h => by
    have hStep : step rule137 n config = config' := by
      simpa [toComputationalMachine] using h
    have hgen := complementSimulationGeneral rule137 n config
    rw [complementRule_rule137] at hgen
    refine ⟨1, ?_⟩
    simp [ComputationalMachine.iterationStep, toComputationalMachine, hgen, hStep]
  halting config h := absurd h (stepNeverNone rule137 n config)

def rule137SimulatesRule110 (n : Nat) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule137 n)
      (toComputationalMachine rule110 n) where
  encode := complementTape n
  commutes := fun config config' h => by
    have hStep : step rule110 n config = config' := by
      simpa [toComputationalMachine] using h
    have hgen := complementSimulationGeneral rule110 n config
    rw [complementRule_rule110] at hgen
    refine ⟨1, ?_⟩
    simp [ComputationalMachine.iterationStep, toComputationalMachine, hgen, hStep]
  halting config h := absurd h (stepNeverNone rule110 n config)

def rule110SimulatesRule193 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule110 n)
      (toComputationalMachine rule193 n) where
  encode := mirrorComplementTape n
  commutes := fun config config' h => by
    have hStep : step rule193 n config = config' := by
      simpa [toComputationalMachine] using h
    have hgen := mirrorComplementSimulation rule193 n hn config
    have hrule : mirrorRule (complementRule rule193) = rule110 := by
      rw [complementRule_rule193, mirrorRule_rule124]
    rw [hrule] at hgen
    refine ⟨1, ?_⟩
    simp [ComputationalMachine.iterationStep, toComputationalMachine, hgen, hStep]
  halting config h := absurd h (stepNeverNone rule193 n config)

def rule193SimulatesRule110 (n : Nat) (hn : n ≥ 3) :
    ComputationalMachine.Simulation
      (toComputationalMachine rule193 n)
      (toComputationalMachine rule110 n) where
  encode := mirrorComplementTape n
  commutes := fun config config' h => by
    have hStep : step rule110 n config = config' := by
      simpa [toComputationalMachine] using h
    have hgen := mirrorComplementSimulation rule110 n hn config
    have hrule : mirrorRule (complementRule rule110) = rule193 := by
      rw [complementRule_rule110, mirrorRule_rule137]
    rw [hrule] at hgen
    refine ⟨1, ?_⟩
    simp [ComputationalMachine.iterationStep, toComputationalMachine, hgen, hStep]
  halting config h := absurd h (stepNeverNone rule110 n config)

end ElementaryCellularAutomaton
