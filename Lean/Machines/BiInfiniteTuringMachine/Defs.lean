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

end BiInfiniteTuringMachine
