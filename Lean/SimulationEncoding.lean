/-
  SimulationEncoding

  Three layers of simulation of machine B by machine A, in increasing strength:

  1. `HaltingSimulation` — only halting preservation. Used for reductions where
     no step correspondence is available (e.g. Smith CTS → (2,3) TM).

  2. `Simulation` — encode + step correspondence (one B-step lifts to some n
     A-steps reaching `encode(b')`) + halting. No decode required. The default
     for most edges. Composes; gives halting preservation.

  3. `SimulationEncoding` — encode + decode + conjugation
     (`step_B(b) = decode (step_A^n (encode b))`) + halting. For edges with a
     natural decode; reads as Moore-style topological conjugacy.

  Each layer comes with an `Overhead` (spatial × temporal). Canonicalization
  of step-results, when needed, is done at the *machine* level (define
  `stepNormalized` and a bisimulation lemma) rather than carried as a field
  of the simulation.
-/

import ComputationalMachine

namespace ComputationalMachine

structure Overhead where
  spatial  : Nat → Nat
  temporal : Nat → Nat

def Overhead.compose (overheadF overheadG : Overhead) : Overhead where
  spatial  := fun n => overheadF.spatial (overheadG.spatial n)
  temporal := fun n => overheadF.temporal (overheadG.spatial n) * overheadG.temporal n

def Overhead.id : Overhead where
  spatial := fun n => n
  temporal := fun _ => 1

/-
  Simulation — minimal simulation of B by A.
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
  HaltingSimulation — weakest layer.
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

/-
  SimulationEncoding — conjugation form.

  Reads as `step_B(b) = decode (step_A^n (encode b))`: one B-step lifts to
  some n A-steps, after which decoding recovers b'. No `roundtrip` field
  (decode-encode is not constrained) and no `normalize` field
  (canonicalization, if needed, is on the machine via `stepNormalized`).

  This is a presentation form for edges that have a natural decode.
  Composition and halting preservation flow through `Simulation`, which
  every edge can also produce when needed.
-/

structure SimulationEncoding (A B : ComputationalMachine) where
  encode : B.Configuration → A.Configuration
  decode : A.Configuration → Option B.Configuration
  /-- Conjugation: one B-step lifts to some n A-steps reaching some `a`,
      and `decode a = some b'`. -/
  commutes : ∀ b b', B.step b = some b' →
    ∃ n a, A.iterationStep n (encode b) = some a ∧ decode a = some b'
  /-- B halting (`step b = none`) implies A halts on `encode b`. -/
  halting : ∀ b, B.step b = none → A.Halts (encode b)

end ComputationalMachine
