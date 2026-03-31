/-
  TuringMachine.Defs

  Shared definitions for Turing machine formalizations.

  Conventions:
  - States are Nat: 0 = halt state, 1..s = active states
  - Symbols are Nat: 0 = blank
  - Direction: L = left, R = right
-/

namespace TuringMachine

inductive Direction where
  | L
  | R
  deriving Repr, DecidableEq, BEq

structure TransitionRule where
  nextState : Nat
  write     : Nat
  direction : Direction
  deriving Repr, DecidableEq, BEq

structure Machine where
  numberOfStates  : Nat
  numberOfSymbols : Nat
  transition : Nat → Nat → TransitionRule

def decodeRule (numberOfStates numberOfSymbols : Nat) (ruleNumber : Nat) : Machine where
  numberOfStates := numberOfStates
  numberOfSymbols := numberOfSymbols
  transition := fun state symbol =>
    let index := state * numberOfSymbols + symbol
    let totalActions := 2 * numberOfStates * numberOfSymbols
    if totalActions == 0 then { nextState := 0, write := 0, direction := Direction.R }
    else
      let action := (ruleNumber / (totalActions ^ index)) % totalActions
      let direction := if action % 2 == 0 then Direction.R else Direction.L
      let rest := action / 2
      { nextState := rest / numberOfSymbols, write := rest % numberOfSymbols, direction := direction }

end TuringMachine
