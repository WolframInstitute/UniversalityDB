/-
  GeneralizedShiftToTuringMachine

  Moore's Theorem 8: any generalized shift can be simulated by a Turing machine.

  Given a GS on alphabet A (|A| = n) with DOD of width w and max shift magnitude m,
  we construct a BiTM that simulates each GS step in τ ≤ 2(w-1) + m TM steps.

  Reference: C. Moore, "Generalized shifts: unpredictability and
  undecidability in dynamical systems", Nonlinearity 4 (1991) 199-230.

  == Construction (Theorem 8, p.218) ==

  The TM operates in three phases per GS step:

  Phase 1 — Read: Starting at cell 0 of the DOD, scan right for w cells,
  accumulating the window contents in the TM's internal state.
  Takes w-1 steps.

  Phase 2 — Write: Write the replacement word back right-to-left.
  Takes w-1 steps.

  Phase 3 — Shift: Move to the new pointer position.
  Takes m steps (the shift magnitude for this transition).

  Total per GS step: (w-1) + (w-1) + m = 2(w-1) + m ≤ 2(w-1) + maxShift.

  Number of TM states ≤ (|Im F| + 1) · (n^w - 1)/(n - 1) + 2(max|F| - 1).

  == Formalization approach ==

  We define:
  1. GSParams: parameters of a GS (alphabet size, window width, max shift, etc.)
  2. toBiTM: construct the BiTM from GSParams
  3. encodeConfig / decodeConfig: configuration mappings
  4. StepSimulation: specification that one GS step = bounded BiTM steps
  5. Computational verification on examples
-/

import Machines.BiInfiniteTuringMachine.Defs
import Machines.GeneralizedShift.Defs

namespace GeneralizedShiftToTuringMachine

open TuringMachine BiInfiniteTuringMachine GeneralizedShift

-- ============================================================================
-- GS parameters
-- ============================================================================

structure GSParams where
  alphabetSize : Nat
  windowWidth : Nat
  maxShift : Nat
  gsTransition : List Nat → GeneralizedShift.ShiftRule
  gsIsActive : List Nat → Bool

def gsMachine (params : GSParams) : GeneralizedShift.Machine where
  alphabetSize := params.alphabetSize
  windowWidth := params.windowWidth
  transition := params.gsTransition
  isActive := params.gsIsActive

-- ============================================================================
-- TM state encoding
-- ============================================================================

-- State layout:
--   0                        : halt
--   1                        : start (about to read cell 0 of window)
--   2 + readOffset           : read phase states
--   writeStateBase + offset  : write phase states
--   shiftStateBase + offset  : shift phase states

def nPow (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => n * nPow n k

-- Read state: at position pos (0..w-1), having accumulated partialCode
def readState (params : GSParams) (pos : Nat) (partialCode : Nat) : Nat :=
  2 + pos * nPow params.alphabetSize params.windowWidth + partialCode

def writeStateBase (params : GSParams) : Nat :=
  2 + params.windowWidth * nPow params.alphabetSize params.windowWidth

-- Write state: at position pos (w-1 down to 0), with windowCode
def writeState (params : GSParams) (pos : Nat) (windowCode : Nat) : Nat :=
  writeStateBase params + pos * nPow params.alphabetSize params.windowWidth + windowCode

def shiftStateBase (params : GSParams) : Nat :=
  writeStateBase params + params.windowWidth * nPow params.alphabetSize params.windowWidth

-- Shift state: remaining steps, direction (0 = right, 1 = left)
def shiftState (params : GSParams) (remaining : Nat) (goLeft : Bool) : Nat :=
  shiftStateBase params + remaining * 2 + if goLeft then 1 else 0

def totalStates (params : GSParams) : Nat :=
  shiftStateBase params + (params.maxShift + 1) * 2

-- ============================================================================
-- Window encoding/decoding as Nat
-- ============================================================================

def encodeWindow (alphabetSize : Nat) (window : List Nat) : Nat :=
  window.foldl (fun acc v => acc * alphabetSize + v) 0

def decodeWindow (alphabetSize : Nat) (windowWidth : Nat) (code : Nat) : List Nat :=
  let rec go (w : Nat) (c : Nat) (acc : List Nat) : List Nat :=
    match w with
    | 0 => acc
    | w' + 1 => go w' (c / alphabetSize) ((c % alphabetSize) :: acc)
  go windowWidth code []

-- ============================================================================
-- Configuration encoding: GS ↔ BiTM
-- ============================================================================

/-- Encode a GS config as a BiTM config.
    The BiTM tape is the GS tape flattened, with the BiTM head at cell 0
    of the GS window. BiTM state = 1 (start of read phase). -/
def encodeConfig (gsConfig : GeneralizedShift.Configuration) : BiInfiniteTuringMachine.Configuration :=
  match gsConfig.cells with
  | [] => { state := 1, left := gsConfig.left, head := 0, right := gsConfig.right }
  | c :: cs => { state := 1, left := gsConfig.left, head := c, right := cs ++ gsConfig.right }

def decodeConfig (windowWidth : Nat) (tmConfig : BiInfiniteTuringMachine.Configuration)
    : Option GeneralizedShift.Configuration :=
  if tmConfig.state ≠ 1 then none
  else
    let cells := tmConfig.head :: tmConfig.right.take (windowWidth - 1)
    let right := tmConfig.right.drop (windowWidth - 1)
    some { left := tmConfig.left, cells := cells, right := right }

-- ============================================================================
-- TM transition function
-- ============================================================================

def getListElem (list : List Nat) (idx : Nat) : Nat :=
  match list[idx]? with
  | some v => v
  | none => 0

def buildTransition (params : GSParams) (state : Nat) (symbol : Nat) : TransitionRule :=
  let shiftDir (goLeft : Bool) := if goLeft then Direction.L else Direction.R
  -- Helper: given a just-computed rule, emit the transition that ends the write
  -- phase and starts the shift. The write has been fully applied; head is at
  -- DOD position 0 (leftmost window cell) pointing right.
  -- We need `rule.shiftMagnitude` moves from here.
  --   0: stay (write repl, go to state 1, move R since we'll read from pos 0 anyway)
  --   1: one move in shift direction, go to state 1
  --  ≥2: one move in shift direction, enter shift phase with (mag - 2) remaining
  let startShift (repl : Nat) (rule : GeneralizedShift.ShiftRule) : TransitionRule :=
    if rule.shiftMagnitude = 0 then
      { nextState := 1, write := repl, direction := Direction.R }
    else if rule.shiftMagnitude = 1 then
      { nextState := 1, write := repl,
        direction := shiftDir rule.shiftLeft }
    else
      { nextState := shiftState params (rule.shiftMagnitude - 2) rule.shiftLeft,
        write := repl,
        direction := shiftDir rule.shiftLeft }
  -- Halt state
  if state = 0 then
    { nextState := 0, write := symbol, direction := Direction.R }
  -- State 1: start of read phase at cell 0
  else if state = 1 then
    if params.windowWidth ≤ 1 then
      let window := [symbol]
      if ¬ params.gsIsActive window then
        { nextState := 0, write := symbol, direction := Direction.R }
      else
        let rule := params.gsTransition window
        let repl := getListElem rule.replacement 0
        startShift repl rule
    else
      { nextState := readState params 1 symbol,
        write := symbol, direction := Direction.R }
  -- Read phase
  else if state ≥ 2 && state < writeStateBase params then
    let offset := state - 2
    let nw := nPow params.alphabetSize params.windowWidth
    let pos := offset / nw
    let partialCode := offset % nw
    let newPartial := partialCode * params.alphabetSize + symbol
    if pos + 1 ≥ params.windowWidth then
      let window := decodeWindow params.alphabetSize params.windowWidth newPartial
      if ¬ params.gsIsActive window then
        { nextState := 0, write := symbol, direction := Direction.L }
      else
        let rule := params.gsTransition window
        let replHere := getListElem rule.replacement (params.windowWidth - 1)
        if params.windowWidth ≤ 1 then
          startShift replHere rule
        else
          { nextState := writeState params (params.windowWidth - 2) newPartial,
            write := replHere, direction := Direction.L }
    else
      { nextState := readState params (pos + 1) newPartial,
        write := symbol, direction := Direction.R }
  -- Write phase
  else if state ≥ writeStateBase params && state < shiftStateBase params then
    let offset := state - writeStateBase params
    let nw := nPow params.alphabetSize params.windowWidth
    let pos := offset / nw
    let windowCode := offset % nw
    let window := decodeWindow params.alphabetSize params.windowWidth windowCode
    let rule := params.gsTransition window
    let replHere := getListElem rule.replacement pos
    if pos = 0 then
      startShift replHere rule
    else
      { nextState := writeState params (pos - 1) windowCode,
        write := replHere, direction := Direction.L }
  -- Shift phase
  else if state ≥ shiftStateBase params then
    let offset := state - shiftStateBase params
    let remaining := offset / 2
    let goLeft := offset % 2 = 1
    let dir := shiftDir goLeft
    if remaining = 0 then
      { nextState := 1, write := symbol, direction := dir }
    else
      { nextState := shiftState params (remaining - 1) goLeft,
        write := symbol, direction := dir }
  else
    { nextState := 0, write := symbol, direction := Direction.R }

def toBiTM (params : GSParams) : TuringMachine.Machine where
  numberOfStates := totalStates params
  numberOfSymbols := params.alphabetSize
  transition := buildTransition params

-- ============================================================================
-- Overhead bounds
-- ============================================================================

def temporalOverhead (params : GSParams) : Nat :=
  2 * (params.windowWidth - 1) + params.maxShift

-- ============================================================================
-- Step simulation specification
-- ============================================================================

def StepSimulation (params : GSParams) : Prop :=
  ∀ (gsConfig gsConfig' : GeneralizedShift.Configuration),
    gsConfig.cells.length = params.windowWidth →
    GeneralizedShift.step (gsMachine params) gsConfig = some gsConfig' →
    ∃ n, n ≤ temporalOverhead params ∧
      BiInfiniteTuringMachine.exactSteps (toBiTM params) (encodeConfig gsConfig) n =
      some (encodeConfig gsConfig')

-- ============================================================================
-- Example: GS with window width 1 (simplest case)
-- ============================================================================

def exampleGS1 : GSParams where
  alphabetSize := 2
  windowWidth := 1
  maxShift := 1
  gsTransition := fun window =>
    match window with
    | [0] => { replacement := [1], shiftMagnitude := 1, shiftLeft := false }
    | [1] => { replacement := [0], shiftMagnitude := 1, shiftLeft := true }
    | _ => { replacement := [0], shiftMagnitude := 0, shiftLeft := false }
  gsIsActive := fun window =>
    match window with
    | [0] => true
    | [1] => true
    | _ => false

#eval do
  let gsConfig : GeneralizedShift.Configuration := { left := [0,0], cells := [1], right := [0,0] }
  let gsConfig' ← GeneralizedShift.step (gsMachine exampleGS1) gsConfig
  return gsConfig'

-- Verify: does the TM simulation match the GS step?
def verifyOneGSStep (params : GSParams) (gsConfig : GeneralizedShift.Configuration) : Option Bool := do
  let gsConfig' ← GeneralizedShift.step (gsMachine params) gsConfig
  let tm := toBiTM params
  let tmStart := encodeConfig gsConfig
  let tmTarget := encodeConfig gsConfig'
  let τ := temporalOverhead params
  let mut found := false
  for i in List.range (τ + 2) do
    match BiInfiniteTuringMachine.exactSteps tm tmStart i with
    | some c => if c == tmTarget then found := true
    | none => pure ()
  return found

def verifyGSToTMSteps (params : GSParams) (gsConfig : GeneralizedShift.Configuration) : Nat → Option Bool
  | 0 => some true
  | n + 1 => do
    let ok ← verifyOneGSStep params gsConfig
    if ¬ ok then return false
    let gsConfig' ← GeneralizedShift.step (gsMachine params) gsConfig
    verifyGSToTMSteps params gsConfig' n

#eval verifyGSToTMSteps exampleGS1
  { left := [0,0,0,0,0], cells := [1], right := [0,0,0,0,0] } 5

-- ============================================================================
-- Example: GS with window width 3 (Moore's examples)
-- ============================================================================

def exampleGS3 : GSParams where
  alphabetSize := 2
  windowWidth := 3
  maxShift := 2
  gsTransition := fun window =>
    match window with
    | [0, 0, 1] => { replacement := [1, 1, 0], shiftMagnitude := 1, shiftLeft := false }
    | [0, 1, 0] => { replacement := [0, 1, 1], shiftMagnitude := 1, shiftLeft := true }
    | [0, 1, 1] => { replacement := [1, 0, 0], shiftMagnitude := 2, shiftLeft := false }
    | [1, 0, 0] => { replacement := [0, 0, 1], shiftMagnitude := 1, shiftLeft := true }
    | [1, 0, 1] => { replacement := [1, 1, 1], shiftMagnitude := 2, shiftLeft := true }
    | [1, 1, 0] => { replacement := [0, 1, 0], shiftMagnitude := 1, shiftLeft := false }
    | _ => { replacement := window, shiftMagnitude := 0, shiftLeft := false }
  gsIsActive := fun window =>
    match window with
    | [0, 0, 0] => false
    | [1, 1, 1] => false
    | _ => true

#eval verifyGSToTMSteps exampleGS3
  { left := [0,0,0,0,0], cells := [0, 1, 0], right := [0,0,0,0,0] } 3

-- ============================================================================
-- Example: verify Theorem 7's output can be simulated back by Theorem 8
-- ============================================================================

-- Take the (2,2) TM, convert to GS via Theorem 7 (fromBiTM),
-- then convert that GS back to a TM via Theorem 8 (toBiTM).
-- The round-trip should work.

end GeneralizedShiftToTuringMachine
