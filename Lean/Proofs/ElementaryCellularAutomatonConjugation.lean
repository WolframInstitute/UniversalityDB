/-
  ElementaryCellularAutomaton.Conjugation

  Klein-4 group of ECA rule conjugations. Two trivial symmetries:

  - Mirror     f(a,b,c) = g(c,b,a)        ↔  tape reversal
  - Complement f(a,b,c) = ¬g(¬a,¬b,¬c)    ↔  bit complement

  They commute and are involutive, so the four rules
    {rule, mirror rule, complement rule, mirror (complement rule)}
  form a Klein-4 orbit.

  For Rule 110 the orbit is {110, 124, 137, 193}.

  - rule110 ↔ rule124 (mirror): proved in `ElementaryCellularAutomatonMirror.lean`
    (kept for backwards compatibility and Integrity registration).
  - rule110 ↔ rule137 (complement): proved here via `complementTape`.
  - rule110 ↔ rule193 (mirror ∘ complement): proved here via
    `reverseTape ∘ complementTape`.

  The mirror argument is reused from the existing file via a generic
  rule-parametric variant `mirrorSimulationGenericGeneral`.
-/

import Machines.ElementaryCellularAutomaton.Defs
import SimulationEncoding
import Proofs.ElementaryCellularAutomatonMirror

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

/-! ## Specific Rule 110 orbit identifications -/

theorem mirrorRule_rule110 : mirrorRule rule110 = rule124 := by
  funext a b c; revert a b c; decide

theorem complementRule_rule110 : complementRule rule110 = rule137 := by
  funext a b c; revert a b c; decide

theorem mirrorRule_rule137 : mirrorRule rule137 = rule193 := by
  funext a b c; revert a b c; decide

theorem complementRule_rule124 : complementRule rule124 = rule193 := by
  funext a b c; revert a b c; decide

/-- Derived: complement is involutive, so complementRule rule137 = rule110. -/
theorem complementRule_rule137 : complementRule rule137 = rule110 := by
  have h := complementRule_involutive rule110
  rw [complementRule_rule110] at h; exact h

/-- Derived: mirror is involutive, so mirrorRule rule124 = rule110. -/
theorem mirrorRule_rule124 : mirrorRule rule124 = rule110 := by
  have h := mirrorRule_involutive rule110
  rw [mirrorRule_rule110] at h; exact h

/-- Derived: complement of rule193 = rule124. -/
theorem complementRule_rule193 : complementRule rule193 = rule124 := by
  have h := complementRule_involutive rule124
  rw [complementRule_rule124] at h; exact h

/-- Derived: mirror of rule193 = rule137. -/
theorem mirrorRule_rule193 : mirrorRule rule193 = rule137 := by
  have h := mirrorRule_involutive rule137
  rw [mirrorRule_rule137] at h; exact h

/-! ## Bit-complement tape transform -/

def complementTape (n : Nat) (tape : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i => flip2 (tape i)

theorem complementTapeInvolutive (n : Nat) (tape : Fin n → Fin 2) :
    complementTape n (complementTape n tape) = tape := by
  funext i; simp [complementTape]

/-- Reverse and complement act on disjoint axes (indices vs values), so they commute. -/
theorem reverseTape_complementTape_comm (n : Nat) (tape : Fin n → Fin 2) :
    reverseTape n (complementTape n tape) = complementTape n (reverseTape n tape) := by
  funext i; simp [reverseTape, complementTape]

/-! ## Generic conjugation lemmas (rule-parametric) -/

/-- One step under `complementRule rule` on a complemented tape equals
    complementing one step under `rule`. No length constraint. -/
theorem complementSimulationGeneral (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n : Nat) (tape : Fin n → Fin 2) :
    step (complementRule rule) n (complementTape n tape) =
    complementTape n (step rule n tape) := by
  funext i
  simp [step, complementTape, complementRule]

/-- Generic mirror simulation (rule-parametric version of the locked
    `mirrorSimulationGeneral`). The rule110/rule124 case in
    `ElementaryCellularAutomatonMirror.lean` is the specialization
    `rule = rule124` after `mirrorRule rule124 = rule110`. -/
theorem mirrorSimulationGenericGeneral
    (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n : Nat) (hn : n ≥ 3) (tape : Fin n → Fin 2) :
    step (mirrorRule rule) n (reverseTape n tape) =
    reverseTape n (step rule n tape) := by
  funext i
  simp only [step, reverseTape, mirrorRule]
  have hi := i.isLt
  congr 1
  · congr 1; exact Fin.ext (reverseRightIsLeft n i.val hn hi)
  · congr 1; exact Fin.ext (reverseLeftIsRight n i.val hn hi)

/-! ## Composed transform: reverse ∘ complement -/

/-- `reverseTape n ∘ complementTape n` — encodes the rule110 ↔ rule193 edge. -/
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
  rw [mirrorSimulationGenericGeneral (complementRule rule) n hn (complementTape n tape),
      complementSimulationGeneral rule n tape]

/-! ## Wrappers: `Simulation` instances for the new edges -/

/-- ECA never halts (step is total), so the halting hypothesis is vacuous. -/
private theorem stepNeverNone (rule : Fin 2 → Fin 2 → Fin 2 → Fin 2) (n : Nat)
    (config : Fin n → Fin 2) :
    (toComputationalMachine rule n).step config ≠ none := by
  simp [toComputationalMachine]

/-- **Rule 110 simulates Rule 137** via bit complement of the tape (σ=1, τ=1). -/
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

/-- **Rule 137 simulates Rule 110** via bit complement of the tape (σ=1, τ=1). -/
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

/-- **Rule 110 simulates Rule 193** via reversal + complement (σ=1, τ=1). -/
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

/-- **Rule 193 simulates Rule 110** via reversal + complement (σ=1, τ=1). -/
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
