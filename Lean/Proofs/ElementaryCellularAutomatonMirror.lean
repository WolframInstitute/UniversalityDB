/-
  ElementaryCellularAutomaton.Mirror

  Proof that ECA Rule 110 simulates ECA Rule 124 (and vice versa)
  via tape reversal. This is a bisimulation with σ = 1, τ = 1.

  Key theorem: rule110(a, b, c) = rule124(c, b, a) for all a, b, c ∈ {0,1}
-/

import Machines.ElementaryCellularAutomaton.Defs

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

end ElementaryCellularAutomaton
