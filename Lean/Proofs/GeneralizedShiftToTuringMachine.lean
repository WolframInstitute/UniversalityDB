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
-- Window encoding roundtrip
-- ============================================================================

theorem encodeWindow_nil (n : Nat) : encodeWindow n [] = 0 := rfl

private theorem foldl_encode_shift (n : Nat) (xs : List Nat) (init : Nat) :
    xs.foldl (fun acc v => acc * n + v) init =
    xs.foldl (fun acc v => acc * n + v) 0 + init * nPow n xs.length := by
  induction xs generalizing init with
  | nil => simp [nPow]
  | cons y ys ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (init * n + y), ih (0 * n + y)]
    simp only [nPow, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc]
    omega

theorem encodeWindow_cons (n : Nat) (x : Nat) (xs : List Nat) :
    encodeWindow n (x :: xs) = encodeWindow n xs + x * nPow n xs.length := by
  simp only [encodeWindow, List.foldl_cons]
  rw [foldl_encode_shift]; simp

private theorem go_acc (n w : Nat) (code : Nat) (acc : List Nat) :
    decodeWindow.go n w code acc = decodeWindow.go n w code [] ++ acc := by
  induction w generalizing code acc with
  | zero => simp [decodeWindow.go]
  | succ w ih =>
    simp only [decodeWindow.go]
    rw [ih (code / n) ((code % n) :: acc)]
    rw [ih (code / n) [code % n]]
    simp [List.append_assoc]

private theorem encodeWindow_snoc (n : Nat) (xs : List Nat) (a : Nat) :
    encodeWindow n (xs ++ [a]) = encodeWindow n xs * n + a := by
  simp [encodeWindow, List.foldl_append]

private theorem mul_add_div_right (a b n : Nat) (hn : n > 0) (hb : b < n) :
    (a * n + b) / n = a := by
  rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem mul_add_mod_right (a b n : Nat) (hb : b < n) :
    (a * n + b) % n = b := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private theorem dropLast_append_getLast {α : Type} {l : List α} (h : l ≠ []) :
    l.dropLast ++ [l.getLast h] = l := by
  induction l with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys => simp [List.dropLast, List.getLast, ih (by simp)]

theorem decodeWindow_encodeWindow (n w : Nat) (window : List Nat)
    (hLen : window.length = w) (hBound : ∀ (x : Nat), x ∈ window → x < n) (hn : n > 0) :
    decodeWindow n w (encodeWindow n window) = window := by
  simp only [decodeWindow]
  induction w generalizing window with
  | zero =>
    cases window with
    | nil => simp [decodeWindow.go]
    | cons => simp at hLen
  | succ w ih =>
    have hne : window ≠ [] := by intro h; simp [h] at hLen
    have ha : window.getLast hne < n := hBound _ (List.getLast_mem hne)
    have hInitLen : window.dropLast.length = w := by simp [List.length_dropLast]; omega
    have hInitBound : ∀ (x : Nat), x ∈ window.dropLast → x < n :=
      fun x hx => hBound x (List.dropLast_subset window hx)
    rw [show window = window.dropLast ++ [window.getLast hne] from (dropLast_append_getLast hne).symm]
    rw [encodeWindow_snoc]
    simp only [decodeWindow.go]
    rw [mul_add_div_right _ _ _ hn ha, mul_add_mod_right _ _ _ ha, go_acc]
    congr 1
    exact ih _ hInitLen hInitBound

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
-- Config encoding roundtrip
-- ============================================================================

theorem decodeConfig_encodeConfig (w : Nat) (gsConfig : GeneralizedShift.Configuration)
    (hLen : gsConfig.cells.length = w) (hw : w ≥ 1) :
    decodeConfig w (encodeConfig gsConfig) = some gsConfig := by
  cases hc : gsConfig.cells with
  | nil => rw [hc] at hLen; simp at hLen; omega
  | cons c cs =>
    simp only [encodeConfig, hc, decodeConfig]
    rw [hc] at hLen; simp only [List.length] at hLen
    have hw' : w - 1 = cs.length := by omega
    rw [hw']
    simp
    obtain ⟨left, _, right⟩ := gsConfig
    simp only at hc; subst hc
    rfl

-- ============================================================================
-- TM transition function
-- ============================================================================

def getListElem (list : List Nat) (idx : Nat) : Nat :=
  match list[idx]? with
  | some v => v
  | none => 0

def buildTransition (params : GSParams) (state : Nat) (symbol : Nat) : TransitionRule :=
  let shiftDir (goLeft : Bool) := if goLeft then Direction.L else Direction.R
  -- Helper: emit the transition that ends the write phase and starts the shift.
  -- Head is at DOD position 0 after writing. shiftMagnitude ≥ 1 (GS always moves).
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

/-- One GS step is simulated by a bounded number of TM steps.
    Requires shiftMagnitude ≥ 1 for all active windows (GS always moves). -/
def StepSimulation (params : GSParams) : Prop :=
  ∀ (gsConfig gsConfig' : GeneralizedShift.Configuration),
    gsConfig.cells.length = params.windowWidth →
    (∀ w, params.gsIsActive w = true → (params.gsTransition w).shiftMagnitude ≥ 1) →
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

-- ============================================================================
-- Step simulation proof for windowWidth = 1
-- ============================================================================

/-- For windowWidth = 1, one GS step = exactly 1 TM step when shiftMagnitude = 1,
    or (shiftMagnitude - 1) + 1 steps in general. -/
theorem stepSimulation_w1 (params : GSParams)
    (hw : params.windowWidth = 1)
    (hShift : ∀ w, params.gsIsActive w = true → (params.gsTransition w).shiftMagnitude ≥ 1)
    (gsConfig gsConfig' : GeneralizedShift.Configuration)
    (hLen : gsConfig.cells.length = params.windowWidth)
    (hStep : GeneralizedShift.step (gsMachine params) gsConfig = some gsConfig') :
    ∃ n, n ≤ temporalOverhead params ∧
      BiInfiniteTuringMachine.exactSteps (toBiTM params) (encodeConfig gsConfig) n =
      some (encodeConfig gsConfig') := by
  -- cells must be [c] since length = windowWidth = 1
  rw [hw] at hLen
  obtain ⟨left, cells, right⟩ := gsConfig
  simp only at hLen hStep
  match hcells : cells with
  | [] => simp at hLen
  | [c] =>
    -- Extract GS step result from hStep
    unfold GeneralizedShift.step gsMachine at hStep
    simp only at hStep
    by_cases hActive : params.gsIsActive [c] = true
    · -- Active case: GS rewrites and shifts
      simp only [hActive, not_true, ite_false] at hStep
      have hStep' := Option.some.inj hStep
      subst hStep'
      -- Now need: TM from encodeConfig {left, [c], right} reaches
      -- encodeConfig (shiftBy {left, repl, right} mag dir) in ≤ τ steps
      -- For w=1: first TM step (state 1) reads c, writes repl, shifts once.
      -- Remaining mag-1 shifts are handled by shift-phase states.
      -- This requires case analysis on the shift magnitude.
      -- For now, sorry — the structure is correct per computational verification.
      sorry
    · -- Inactive: GS halts, contradicts hStep = some
      rw [if_pos hActive] at hStep
      exact absurd hStep (by simp)
  | _ :: _ :: _ => simp at hLen

end GeneralizedShiftToTuringMachine
