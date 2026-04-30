/-
  BiInfiniteTuringMachine.Defs

  Formalization of bi-infinite tape Turing machines.

  Key differences from one-sided TM:
  - Tape is bi-infinite: represented as (left, head, right) where
    left and right are infinite in both directions
  - No boundary-based halting: halts when state = 0
-/

import Machines.TuringMachine.Defs
import ComputationalMachine

namespace BiInfiniteTuringMachine

open TuringMachine

structure Configuration where
  state : Nat
  left  : List Nat
  head  : Nat
  right : List Nat
  deriving DecidableEq, BEq, Repr

def isHalted (config : Configuration) : Bool :=
  config.state == 0

def readHead (list : List Nat) : Nat × List Nat :=
  match list with
  | [] => (0, [])
  | x :: xs => (x, xs)

def step (machine : Machine) (config : Configuration) : Option Configuration :=
  if config.state == 0 then none
  else
    let rule := machine.transition config.state config.head
    match rule.direction with
    | Direction.L =>
      let (newHead, newLeft) := readHead config.left
      some { state := rule.nextState,
             left  := newLeft,
             head  := newHead,
             right := rule.write :: config.right }
    | Direction.R =>
      let (newHead, newRight) := readHead config.right
      some { state := rule.nextState,
             left  := rule.write :: config.left,
             head  := newHead,
             right := newRight }

def evaluate (machine : Machine) (config : Configuration) : Nat → Option Configuration
  | 0 => if isHalted config then some config else none
  | fuel + 1 =>
    if isHalted config then some config
    else match step machine config with
    | none => some config
    | some config' => evaluate machine config' fuel

def Halts (machine : Machine) (config : Configuration) : Prop :=
  ∃ fuel result, evaluate machine config fuel = some result

def exactSteps (machine : Machine) (config : Configuration) : Nat → Option Configuration
  | 0 => some config
  | n + 1 =>
    match step machine config with
    | none => none
    | some config' => exactSteps machine config' n

-- ============================================================================
-- Wolfram's (2,3) Universal Turing Machine
-- ============================================================================

def wolfram23 : Machine where
  numberOfStates := 3
  numberOfSymbols := 3
  transition := fun state symbol =>
    match state, symbol with
    | 1, 0 => { nextState := 2, write := 1, direction := Direction.R }
    | 1, 1 => { nextState := 1, write := 2, direction := Direction.L }
    | 1, 2 => { nextState := 1, write := 1, direction := Direction.L }
    | 2, 0 => { nextState := 1, write := 2, direction := Direction.L }
    | 2, 1 => { nextState := 2, write := 2, direction := Direction.R }
    | 2, 2 => { nextState := 1, write := 0, direction := Direction.R }
    | _, _ => { nextState := 0, write := 0, direction := Direction.R }

def wolfram23Initial : Configuration :=
  { state := 1, left := [], head := 0, right := [] }

theorem wolfram23Step1 :
    step wolfram23 wolfram23Initial =
    some { state := 2, left := [1], head := 0, right := [] } := by
  native_decide

theorem wolfram23Step2 :
    exactSteps wolfram23 wolfram23Initial 2 =
    some { state := 1, left := [], head := 1, right := [2] } := by
  native_decide

theorem wolfram23Runs10 :
    evaluate wolfram23 wolfram23Initial 10 = none := by
  native_decide

theorem wolfram23Runs20 :
    evaluate wolfram23 wolfram23Initial 20 = none := by
  native_decide

def toComputationalMachine (machine : TuringMachine.Machine) : ComputationalMachine where
  Configuration := Configuration
  step := step machine

theorem iterationStep_eq_exactSteps (machine : TuringMachine.Machine) (config : Configuration) (n : Nat) :
    (toComputationalMachine machine).iterationStep n config = exactSteps machine config n := by
  induction n generalizing config with
  | zero => rfl
  | succ n ih =>
    simp [ComputationalMachine.iterationStep, toComputationalMachine, exactSteps]
    cases step machine config with
    | none => rfl
    | some config' => exact ih config'

-- ============================================================================
-- Trailing-zero normalization (canonicalize bi-infinite tape representation)
-- ============================================================================

/-- Strip trailing zeros from a finite tape. Both `[]` and `[0, 0, ...]`
    represent the same bi-infinite blank tape; we pick `[]` as canonical. -/
def stripTrailingZeros : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let tail := stripTrailingZeros xs
    if tail.isEmpty && x == 0 then [] else x :: tail

/-- Canonicalize a configuration by stripping trailing zeros from both tapes. -/
def stripConfig (config : Configuration) : Configuration :=
  { config with
    left  := stripTrailingZeros config.left
    right := stripTrailingZeros config.right }

/-- Normalized BiTM step: post-strips trailing zeros from both tapes after
    each step. Lands in canonical form, so simulations against this variant
    enjoy strict-equality `commutes`. -/
def stepNormalized (machine : TuringMachine.Machine) (config : Configuration) : Option Configuration :=
  (step machine config).map stripConfig

def exactStepsNormalized (machine : TuringMachine.Machine) (config : Configuration) : Nat → Option Configuration
  | 0 => some config
  | n + 1 =>
    match stepNormalized machine config with
    | none => none
    | some config' => exactStepsNormalized machine config' n

def toComputationalMachineNormalized (machine : TuringMachine.Machine) : ComputationalMachine where
  Configuration := Configuration
  step := stepNormalized machine

theorem iterationStep_normalized_eq_exactSteps (machine : TuringMachine.Machine) (config : Configuration) (n : Nat) :
    (toComputationalMachineNormalized machine).iterationStep n config = exactStepsNormalized machine config n := by
  induction n generalizing config with
  | zero => rfl
  | succ n ih =>
    simp [ComputationalMachine.iterationStep, toComputationalMachineNormalized, exactStepsNormalized]
    cases stepNormalized machine config with
    | none => rfl
    | some config' => exact ih config'

-- ============================================================================
-- Auxiliary list lemmas for `stripTrailingZeros`
-- ============================================================================

@[simp] theorem stripTrailingZeros_nil :
    stripTrailingZeros ([] : List Nat) = [] := rfl

/-- The head (default 0) is invariant under stripping. -/
theorem stripTrailingZeros_headD (xs : List Nat) :
    (stripTrailingZeros xs).headD 0 = xs.headD 0 := by
  cases xs with
  | nil => rfl
  | cons x xs' =>
    simp only [List.headD, stripTrailingZeros]
    by_cases h : ((stripTrailingZeros xs').isEmpty && (x == 0)) = true
    · simp only [h, ite_true]
      simp at h; exact h.2.symm
    · rw [if_neg h]

/-- Strip commutes with `tail`. -/
theorem stripTrailingZeros_tail (xs : List Nat) :
    stripTrailingZeros xs.tail = (stripTrailingZeros xs).tail := by
  cases xs with
  | nil => rfl
  | cons x xs' =>
    simp only [List.tail_cons, stripTrailingZeros]
    by_cases h : ((stripTrailingZeros xs').isEmpty && (x == 0)) = true
    · rw [if_pos h]; simp
      exact List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp h).1
    · rw [if_neg h]; simp

/-- If two lists have equal strips, prepending the same element preserves
    equal strips. -/
theorem stripTrailingZeros_cons_congr (x : Nat) (xs ys : List Nat)
    (h : stripTrailingZeros xs = stripTrailingZeros ys) :
    stripTrailingZeros (x :: xs) = stripTrailingZeros (x :: ys) := by
  simp only [stripTrailingZeros]
  rw [show (stripTrailingZeros xs).isEmpty = (stripTrailingZeros ys).isEmpty from by rw [h]]
  rw [show stripTrailingZeros xs = stripTrailingZeros ys from h]

/-- Strip is idempotent. Follows from `_cons_congr` and `headD`/`tail` lemmas. -/
theorem stripTrailingZeros_idempotent (xs : List Nat) :
    stripTrailingZeros (stripTrailingZeros xs) = stripTrailingZeros xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    simp only [stripTrailingZeros]
    by_cases h : ((stripTrailingZeros xs').isEmpty && (x == 0)) = true
    · rw [if_pos h]; rfl
    · rw [if_neg h]
      simp only [stripTrailingZeros, ih]
      rw [if_neg h]

/-- Cons-strip distribute: stripping `a :: stripTrailingZeros xs` is the
    same as stripping `a :: xs`. -/
theorem stripTrailingZeros_cons_strip (a : Nat) (xs : List Nat) :
    stripTrailingZeros (a :: stripTrailingZeros xs) = stripTrailingZeros (a :: xs) :=
  (stripTrailingZeros_cons_congr a (stripTrailingZeros xs) xs (stripTrailingZeros_idempotent xs))

-- ============================================================================
-- Bisimulation: `step` and `stepNormalized` agree modulo `stripConfig`.
-- ============================================================================

/-- `readHead` is just `(headD 0, tail)`. -/
theorem readHead_eq (xs : List Nat) : readHead xs = (xs.headD 0, xs.tail) := by
  cases xs <;> rfl

/-- The bisimulation lemma: stripping the input first does not change the
    canonical (post-stripped) output. Concretely:

      `(step machine c).map stripConfig = stepNormalized machine (stripConfig c)`

    This is the "step is well-defined modulo trailing-zero canonicalization"
    statement. Bridges the standard step (locked semantics) with the
    normalized variant. -/
theorem step_stripConfig_bisim (machine : TuringMachine.Machine) (c : Configuration) :
    (step machine c).map stripConfig = stepNormalized machine (stripConfig c) := by
  unfold stepNormalized step
  have hState : (stripConfig c).state = c.state := rfl
  have hHead : (stripConfig c).head = c.head := rfl
  rw [hState, hHead]
  by_cases hs : c.state == 0
  · simp [hs]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    -- Reduce both sides via readHead_eq, then split by direction.
    cases hdir : (machine.transition c.state c.head).direction with
    | L =>
      simp only [readHead_eq, stripConfig, Option.map_some]
      apply congrArg some
      congr 1
      · -- stripTrailingZeros c.left.tail = stripTrailingZeros (stripTrailingZeros c.left).tail
        rw [stripTrailingZeros_tail (stripTrailingZeros c.left),
            stripTrailingZeros_idempotent, ← stripTrailingZeros_tail]
      · -- c.left.headD 0 = (stripTrailingZeros c.left).headD 0
        exact (stripTrailingZeros_headD c.left).symm
      · -- stripTrailingZeros (write :: c.right) =
        --   stripTrailingZeros (write :: stripTrailingZeros c.right)
        exact (stripTrailingZeros_cons_strip _ _).symm
    | R =>
      simp only [readHead_eq, stripConfig, Option.map_some]
      apply congrArg some
      congr 1
      · exact (stripTrailingZeros_cons_strip _ _).symm
      · exact (stripTrailingZeros_headD c.right).symm
      · rw [stripTrailingZeros_tail (stripTrailingZeros c.right),
            stripTrailingZeros_idempotent, ← stripTrailingZeros_tail]

end BiInfiniteTuringMachine
