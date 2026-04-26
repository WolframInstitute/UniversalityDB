/-
  GeneralizedShift.Defs

  Generalized shifts on bi-infinite tapes (Moore 1991).

  Reference: C. Moore, "Generalized shifts: unpredictability and
  undecidability in dynamical systems", Nonlinearity 4 (1991) 199-230.

  == Paper definition (equation 2) ==

  A generalized shift acts on bi-infinite sequences a ∈ A^Z:
    Φ : a ↦ σ^{F(a)}(a ⊛ G(a))
  where F : A^Z → Z gives a data-dependent shift amount and
  G : A^Z → (A ∪ {∅})^Z specifies cell modifications.
  Both F and G have finite domain of dependence (DOD) of width w.

  == Formalization ==

  Configuration = (left, cells, right) where:
  - cells : List Nat of length windowWidth (the DOD window)
  - left  : List Nat (tape extending left, head = nearest)
  - right : List Nat (tape extending right, head = nearest)

  Machine = (alphabetSize, windowWidth, transition, isActive) where:
  - transition : List Nat → ShiftRule maps window contents to
    (replacement, shiftMagnitude, shiftLeft)
  - isActive : List Nat → Bool determines if the window is active

  Shift moves the window pointer left or right by shiftMagnitude steps,
  each step consuming one cell from one side and producing one on the other.
-/

import Machines.TuringMachine.Defs
import ComputationalMachine

namespace GeneralizedShift

open TuringMachine

structure ShiftRule where
  replacement    : List Nat
  shiftMagnitude : Nat
  shiftLeft      : Bool
  deriving DecidableEq, BEq, Repr

structure Machine where
  alphabetSize : Nat
  windowWidth  : Nat
  transition   : List Nat → ShiftRule
  isActive     : List Nat → Bool

structure Configuration where
  left  : List Nat
  cells : List Nat
  right : List Nat
  deriving DecidableEq, BEq, Repr

-- Shift the window one step right: leftmost cell goes to left tape,
-- one cell from right tape enters as rightmost cell.
def shiftRightOne (config : Configuration) : Configuration :=
  let newLeft := match config.cells with
    | [] => config.left
    | c :: _ => c :: config.left
  let tail := config.cells.drop 1
  match config.right with
  | [] => { left := newLeft, cells := tail ++ [0], right := [] }
  | r :: rs => { left := newLeft, cells := tail ++ [r], right := rs }

-- Shift the window one step left: rightmost cell goes to right tape,
-- one cell from left tape enters as leftmost cell.
def shiftLeftOne (config : Configuration) : Configuration :=
  let lastCell := config.cells.getLastD 0
  let newRight := lastCell :: config.right
  let init := config.cells.dropLast
  match config.left with
  | [] => { left := [], cells := 0 :: init, right := newRight }
  | l :: ls => { left := ls, cells := l :: init, right := newRight }

def shiftBy (config : Configuration) (magnitude : Nat) (goLeft : Bool) : Configuration :=
  match magnitude with
  | 0 => config
  | n + 1 =>
    let config' := if goLeft then shiftLeftOne config else shiftRightOne config
    shiftBy config' n goLeft

/-- Strip trailing zeros from a tape (far-end blank cells).
    This normalizes the tape representation so that `[]` and `[0]` are
    not distinguished (both represent blank tape at infinity). -/
def stripTrailingZeros : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let tail := stripTrailingZeros xs
    if tail.isEmpty && x == 0 then [] else x :: tail

@[simp] theorem stripTrailingZeros_nil : stripTrailingZeros ([] : List Nat) = [] := rfl

theorem stripTrailingZeros_idempotent (xs : List Nat) :
    stripTrailingZeros (stripTrailingZeros xs) = stripTrailingZeros xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    simp only [stripTrailingZeros]
    split
    · simp [stripTrailingZeros]
    · rename_i h; simp [stripTrailingZeros, ih, h]

@[simp] theorem stripTrailingZeros_reconstruct (xs : List Nat) :
    stripTrailingZeros
      ((match xs with | [] => 0 | l :: _ => l) :: xs.tail) =
    stripTrailingZeros xs := by
  cases xs with
  | nil => simp [stripTrailingZeros]
  | cons _ _ => rfl

theorem stripTrailingZeros_cons_strip (a : Nat) (xs : List Nat) :
    stripTrailingZeros (a :: stripTrailingZeros xs) = stripTrailingZeros (a :: xs) := by
  simp only [stripTrailingZeros, stripTrailingZeros_idempotent]

def step (machine : Machine) (config : Configuration) : Option Configuration :=
  if ¬ machine.isActive config.cells then none
  else
    let rule := machine.transition config.cells
    let config' := { config with cells := rule.replacement }
    some (shiftBy config' rule.shiftMagnitude rule.shiftLeft)

def exactSteps (machine : Machine) (config : Configuration) : Nat → Option Configuration
  | 0 => some config
  | n + 1 =>
    match step machine config with
    | none => none
    | some config' => exactSteps machine config' n

def evaluate (machine : Machine) (config : Configuration) : Nat → Option Configuration
  | 0 => if ¬ machine.isActive config.cells then some config else none
  | fuel + 1 =>
    if ¬ machine.isActive config.cells then some config
    else match step machine config with
    | none => some config
    | some config' => evaluate machine config' fuel

def Halts (machine : Machine) (config : Configuration) : Prop :=
  ∃ fuel result, evaluate machine config fuel = some result

def toComputationalMachine (machine : Machine) : ComputationalMachine where
  Configuration := Configuration
  step := step machine

theorem iterationStep_eq_exactSteps (machine : Machine) (config : Configuration) (n : Nat) :
    (toComputationalMachine machine).iterationStep n config = exactSteps machine config n := by
  induction n generalizing config with
  | zero => rfl
  | succ n ih =>
    simp [ComputationalMachine.iterationStep, toComputationalMachine, exactSteps]
    cases step machine config with
    | none => rfl
    | some config' => exact ih config'


end GeneralizedShift
