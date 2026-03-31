/-
  SimulationEncoding

  A simulation encoding of machine B by machine A: a morphism in the category
  of computational machines. Composition gives transitivity of encodings.

  The commutation property states that one B-step lifts to a bounded
  number of A-steps on encoded configurations.
-/

import ComputationalMachine

namespace ComputationalMachine

structure SimulationEncoding (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  decode : A.Configuration → Option B.Configuration
  roundtrip : ∀ config : B.Configuration, decode (encode config) = some config
  commutes : ∀ (config config' : B.Configuration),
    B.step config = some config' →
    ∃ n, A.iterationStep n (encode config) = some (encode config')

structure Overhead where
  spatial  : Nat → Nat
  temporal : Nat → Nat

def SimulationEncoding.id (machine : ComputationalMachine) : SimulationEncoding machine machine where
  encode := fun config => config
  decode := fun config => some config
  roundtrip := by intro config; rfl
  commutes := by intro config config' h; exact ⟨1, by simp [iterationStep, h]⟩

def SimulationEncoding.compose {A B C : ComputationalMachine}
    (f : SimulationEncoding A B) (g : SimulationEncoding B C) : SimulationEncoding A C where
  encode := f.encode ∘ g.encode
  decode := fun a => f.decode a >>= g.decode
  roundtrip := by
    intro config
    simp [Function.comp]
    rw [f.roundtrip (g.encode config)]
    simp [g.roundtrip config]
  commutes := by
    intro config config' h
    obtain ⟨m, hm⟩ := g.commutes config config' h
    obtain ⟨numberOfSteps, hn⟩ := liftSteps f g.encode config config' m hm
    exact ⟨numberOfSteps, hn⟩
  where
    liftSteps {α : Type} {A B : ComputationalMachine} (f : SimulationEncoding A B) (enc : α → B.Configuration)
        (config config' : α) (m : Nat) :
        B.iterationStep m (enc config) = some (enc config') →
        ∃ n, A.iterationStep n (f.encode (enc config)) = some (f.encode (enc config')) :=
      fun h => liftGeneral f _ _ m h
    liftGeneral {A B : ComputationalMachine} (f : SimulationEncoding A B)
        (b b' : B.Configuration) (m : Nat) :
        B.iterationStep m b = some b' →
        ∃ n, A.iterationStep n (f.encode b) = some (f.encode b') := by
      intro h
      induction m generalizing b with
      | zero =>
        simp [iterationStep] at h
        exact ⟨0, by simp [iterationStep, h]⟩
      | succ m ih =>
        simp [iterationStep] at h
        cases hStep : B.step b with
        | none => simp [hStep] at h
        | some mid =>
          simp [hStep] at h
          obtain ⟨k, hk⟩ := f.commutes b mid hStep
          obtain ⟨j, hj⟩ := ih mid h
          exact ⟨k + j, by rw [iterationStep_add]; simp [hk, hj]⟩

def Overhead.compose (overheadF overheadG : Overhead) : Overhead where
  spatial  := fun n => overheadF.spatial (overheadG.spatial n)
  temporal := fun n => overheadF.temporal (overheadG.spatial n) * overheadG.temporal n

def Overhead.id : Overhead where
  spatial := fun n => n
  temporal := fun _ => 1

end ComputationalMachine
