/-
  TagSystem.Defs

  Formalization of 2-tag systems and cyclic tag systems.
  These are intermediate computational models in universality proofs:
    Turing Machine → 2-Tag System → Cyclic Tag System → (Rule 110 / (2,3) TM)
-/

import ComputationalMachine

namespace TagSystem

-- ============================================================================
-- 2-Tag Systems
-- ============================================================================

structure Tag (alphabetSize : Nat) where
  productions : Fin alphabetSize → List (Fin alphabetSize)

abbrev TagConfiguration (alphabetSize : Nat) := List (Fin alphabetSize)

def tagIsHalted {alphabetSize : Nat} (config : TagConfiguration alphabetSize) : Bool :=
  config.length < 2

def Tag.step {alphabetSize : Nat} (tagSystem : Tag alphabetSize) (config : TagConfiguration alphabetSize) : Option (TagConfiguration alphabetSize) :=
  match config with
  | [] => none
  | [_] => none
  | a :: _ :: rest => some (rest ++ tagSystem.productions a)

def Tag.evaluate {alphabetSize : Nat} (tagSystem : Tag alphabetSize) (config : TagConfiguration alphabetSize) : Nat → Option (TagConfiguration alphabetSize)
  | 0 => if tagIsHalted config then some config else none
  | fuel + 1 =>
    if tagIsHalted config then some config
    else match tagSystem.step config with
      | none => some config
      | some config' => tagSystem.evaluate config' fuel

def Tag.Halts {alphabetSize : Nat} (tagSystem : Tag alphabetSize) (config : TagConfiguration alphabetSize) : Prop :=
  ∃ fuel result, tagSystem.evaluate config fuel = some result

-- ============================================================================
-- Basic lemmas for Tag
-- ============================================================================

theorem Tag.evaluateStep {alphabetSize : Nat} (tagSystem : Tag alphabetSize) (config config' : TagConfiguration alphabetSize) (fuel : Nat)
    (hnh : tagIsHalted config = false) (hs : tagSystem.step config = some config') :
    tagSystem.evaluate config (fuel + 1) = tagSystem.evaluate config' fuel := by
  simp [evaluate, hnh, hs]

theorem Tag.evaluateHalted {alphabetSize : Nat} (tagSystem : Tag alphabetSize) (config : TagConfiguration alphabetSize) (fuel : Nat)
    (hh : tagIsHalted config = true) :
    tagSystem.evaluate config fuel = some config := by
  cases fuel with
  | zero => simp [evaluate, hh]
  | succ n => simp [evaluate, hh]

theorem Tag.stepNoneIffHalted {alphabetSize : Nat} (tagSystem : Tag alphabetSize) (config : TagConfiguration alphabetSize) :
  tagSystem.step config = none ↔ tagIsHalted config = true := by
  dsimp [Tag.step, tagIsHalted]
  cases config with
  | nil => simp
  | cons head tail =>
    cases tail with
    | nil => simp
    | cons head' tail' =>
      simp

theorem Tag.evaluateAdd {alphabetSize : Nat} (tagSystem : Tag alphabetSize) (n m : Nat) (config mid result : TagConfiguration alphabetSize) :
  tagSystem.evaluate config n = some mid → tagSystem.evaluate mid m = some result → tagSystem.evaluate config (n + m) = some result := by
  induction n generalizing config with
  | zero =>
    dsimp [Tag.evaluate]
    split
    · intro h1 h2
      injection h1 with e; subst e
      exact (by rw [Nat.zero_add]; exact h2)
    · intro h1
      contradiction
  | succ n ih =>
    dsimp [Tag.evaluate]
    split
    · rename_i hHalt
      intro h1 h2
      injection h1 with e; subst e
      have h3 := Tag.evaluateHalted tagSystem config (n + 1 + m) hHalt
      have h4 := Tag.evaluateHalted tagSystem config m hHalt
      rw [h4] at h2
      injection h2 with e; subst e
      exact h3
    · rename_i hNotHalt
      intro h1 h2
      cases hStep : tagSystem.step config with
      | none =>
        have hHalt2 : tagIsHalted config = true := (Tag.stepNoneIffHalted tagSystem config).mp hStep
        rw [hHalt2] at hNotHalt
        contradiction
      | some config' =>
        rw [hStep] at h1
        have hm := ih config' h1 h2
        rw [Nat.add_right_comm]
        have hHaltFalse : tagIsHalted config = false := by cases hTag : tagIsHalted config <;> simp_all
        rw [Tag.evaluateStep tagSystem config config' (n + m) hHaltFalse hStep]
        exact hm

def Tag.toComputationalMachine {alphabetSize : Nat} (tagSystem : Tag alphabetSize) : ComputationalMachine where
  Configuration := TagConfiguration alphabetSize
  step := tagSystem.step

-- ============================================================================
-- Cyclic Tag Systems
-- ============================================================================

structure CyclicTagSystem where
  appendants : List (List Bool)
  nonempty : appendants.length > 0

structure CyclicTagSystemConfiguration where
  data : List Bool
  phase : Nat
  deriving DecidableEq, BEq, Repr

def cyclicTagIsHalted (config : CyclicTagSystemConfiguration) : Bool :=
  config.data.isEmpty

def CyclicTagSystem.currentAppendant (cyclicTagSystem : CyclicTagSystem) (phase : Nat) : List Bool :=
  cyclicTagSystem.appendants.get ⟨phase % cyclicTagSystem.appendants.length, Nat.mod_lt _ cyclicTagSystem.nonempty⟩

def CyclicTagSystem.step (cyclicTagSystem : CyclicTagSystem) (config : CyclicTagSystemConfiguration) : Option CyclicTagSystemConfiguration :=
  match config.data with
  | [] => none
  | head :: rest =>
    let newData := if head then rest ++ cyclicTagSystem.currentAppendant config.phase else rest
    some { data := newData, phase := (config.phase + 1) % cyclicTagSystem.appendants.length }

def CyclicTagSystem.evaluate (cyclicTagSystem : CyclicTagSystem) (config : CyclicTagSystemConfiguration) : Nat → Option CyclicTagSystemConfiguration
  | 0 => if cyclicTagIsHalted config then some config else none
  | fuel + 1 =>
    if cyclicTagIsHalted config then some config
    else match cyclicTagSystem.step config with
      | none => some config
      | some config' => cyclicTagSystem.evaluate config' fuel

def CyclicTagSystem.Halts (cyclicTagSystem : CyclicTagSystem) (config : CyclicTagSystemConfiguration) : Prop :=
  ∃ fuel result, cyclicTagSystem.evaluate config fuel = some result

def CyclicTagSystem.exactSteps (cyclicTagSystem : CyclicTagSystem) (config : CyclicTagSystemConfiguration) : Nat → Option CyclicTagSystemConfiguration
  | 0 => some config
  | n + 1 =>
    match cyclicTagSystem.step config with
    | none => none
    | some config' => cyclicTagSystem.exactSteps config' n

def Tag.iterationStep_eq {alphabetSize : Nat} (tagSystem : Tag alphabetSize)
    (config : TagConfiguration alphabetSize) (n : Nat) :
    (tagSystem.toComputationalMachine).iterationStep n config =
    match n with
    | 0 => some config
    | n + 1 => tagSystem.step config >>= fun c => (tagSystem.toComputationalMachine).iterationStep n c := by
  cases n with
  | zero => rfl
  | succ n => rfl

def CyclicTagSystem.toComputationalMachine (cts : CyclicTagSystem) : ComputationalMachine where
  Configuration := CyclicTagSystemConfiguration
  step := cts.step

theorem CyclicTagSystem.iterationStep_eq_exactSteps (cts : CyclicTagSystem)
    (config : CyclicTagSystemConfiguration) (n : Nat) :
    (cts.toComputationalMachine).iterationStep n config = cts.exactSteps config n := by
  induction n generalizing config with
  | zero => rfl
  | succ n ih =>
    simp [ComputationalMachine.iterationStep, toComputationalMachine, exactSteps]
    cases cts.step config with
    | none => rfl
    | some config' => exact ih config'

-- ============================================================================
-- Basic lemmas
-- ============================================================================

theorem CyclicTagSystem.evaluateStep (cyclicTagSystem : CyclicTagSystem) (config config' : CyclicTagSystemConfiguration) (fuel : Nat)
    (hnh : cyclicTagIsHalted config = false) (hs : cyclicTagSystem.step config = some config') :
    cyclicTagSystem.evaluate config (fuel + 1) = cyclicTagSystem.evaluate config' fuel := by
  simp [evaluate, hnh, hs]

theorem CyclicTagSystem.evaluateHalted (cyclicTagSystem : CyclicTagSystem) (config : CyclicTagSystemConfiguration) (fuel : Nat)
    (hh : cyclicTagIsHalted config = true) :
    cyclicTagSystem.evaluate config fuel = some config := by
  cases fuel with
  | zero => simp [evaluate, hh]
  | succ n => simp [evaluate, hh]

-- ============================================================================
-- Examples
-- ============================================================================

def exampleCyclicTagSystem : CyclicTagSystem where
  appendants := [[true]]
  nonempty := by simp

def exampleCyclicTagSystemInitial : CyclicTagSystemConfiguration :=
  { data := [false, true], phase := 0 }

theorem exampleCyclicTagSystemStep1 :
    exampleCyclicTagSystem.step exampleCyclicTagSystemInitial = some { data := [true], phase := 0 } := by
  native_decide

theorem exampleCyclicTagSystemStep2 :
    (do let s1 ← exampleCyclicTagSystem.step exampleCyclicTagSystemInitial; exampleCyclicTagSystem.step s1) =
    some { data := [true], phase := 0 } := by
  native_decide

end TagSystem
