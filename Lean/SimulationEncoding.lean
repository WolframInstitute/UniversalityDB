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

/-
  Simulation

  A minimal simulation of machine B by machine A: encode + step correspondence + halting.
  No decode or roundtrip required. Sufficient to derive halting preservation and to compose.
-/

structure Simulation (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  commutes : ∀ (config config' : B.Configuration),
    B.step config = some config' →
    ∃ n, A.iterationStep n (encode config) = some (encode config')
  halting : ∀ config, B.step config = none → A.Halts (encode config)

def Simulation.id (machine : ComputationalMachine) : Simulation machine machine where
  encode := fun config => config
  commutes := by intro config config' h; exact ⟨1, by simp [iterationStep, h]⟩
  halting := by intro config h; exact ⟨1, by simp [iterationStep, h]⟩

private theorem Simulation.liftGeneral {A B : ComputationalMachine} (f : Simulation A B)
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

def Simulation.halting_preserved {A B : ComputationalMachine} (sim : Simulation A B)
    (config : B.Configuration) (h : B.Halts config) : A.Halts (sim.encode config) := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing config with
  | zero => simp [iterationStep] at hn
  | succ n ih =>
    simp [iterationStep] at hn
    cases hStep : B.step config with
    | none =>
      exact sim.halting config hStep
    | some config' =>
      simp [hStep] at hn
      obtain ⟨k, hk⟩ := sim.commutes config config' hStep
      obtain ⟨m, hm⟩ := ih config' hn
      exact ⟨k + m, by rw [iterationStep_add]; simp [hk, hm]⟩

def Simulation.compose {A B C : ComputationalMachine}
    (f : Simulation A B) (g : Simulation B C) : Simulation A C where
  encode := f.encode ∘ g.encode
  commutes := by
    intro config config' h
    obtain ⟨m, hm⟩ := g.commutes config config' h
    exact f.liftGeneral _ _ m hm
  halting := by
    intro config h
    exact f.halting_preserved (g.encode config) (g.halting config h)

/-
  HaltingSimulation

  The weakest simulation notion: only halting preservation.
  Used for reductions where step correspondence is not available (e.g. Smith CTS → (2,3) TM).
-/

structure HaltingSimulation (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  preserves_halting : ∀ config, B.Halts config → A.Halts (encode config)

def Simulation.toHaltingSimulation {A B : ComputationalMachine}
    (sim : Simulation A B) : HaltingSimulation A B where
  encode := sim.encode
  preserves_halting := sim.halting_preserved

def HaltingSimulation.compose {A B C : ComputationalMachine}
    (f : HaltingSimulation A B) (g : HaltingSimulation B C) : HaltingSimulation A C where
  encode := f.encode ∘ g.encode
  preserves_halting := by
    intro config h
    exact f.preserves_halting (g.encode config) (g.preserves_halting config h)

def SimulationEncoding.toSimulation {A B : ComputationalMachine}
    (se : SimulationEncoding A B)
    (h_halting : ∀ config, B.step config = none → A.Halts (se.encode config)) :
    Simulation A B where
  encode := se.encode
  commutes := se.commutes
  halting := h_halting

/-
  SimulationViaDecode

  A more flexible simulation framework where commutes is expressed via decode
  modulo a `normalize` operation on B-configurations. Reads as conjugation:

      decode ∘ A^n ∘ encode  =  some ∘ normalize ∘ B.step

  i.e., running A and decoding gives the *normalized* form of B's next state.
  When `normalize := id`, this is strict conjugation. When `normalize` is
  nontrivial (e.g., trailing-zero stripping for the TM→GS edge), the decode
  contract works modulo the equivalence induced by `normalize`.

  Used for the TM→GS edge where the GS source's `[0]` phantom on previously
  empty tapes is absorbed by `normalize` on the BiTM target side.
-/

structure SimulationViaDecode (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  decode : A.Configuration → Option B.Configuration
  /-- Canonicalization on B-configurations. For "no phantom" cases, take
      `normalize := id`. For cases with redundant representation
      (e.g., trailing-zero list tapes), `normalize` strips the redundancy. -/
  normalize : B.Configuration → B.Configuration
  /-- Roundtrip: encode then decode recovers the normalized form. -/
  roundtrip : ∀ b, decode (encode b) = some (normalize b)
  /-- Conjugation: one B-step lifts to some n A-steps reaching `a`, and
      `a` decodes to the normalized form of `b'`. -/
  commutes : ∀ b b', B.step b = some b' →
    ∃ n a, A.iterationStep n (encode b) = some a ∧
           decode a = some (normalize b')
  /-- B halting (`step b = none`) implies A halts on encode b. -/
  halting : ∀ b, B.step b = none → A.Halts (encode b)

end ComputationalMachine
