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

  == Formalization approach ==

  The TM's internal state is modeled as a TMPhase inductive type:
    halt | start | read pos partial | write pos code | shift remaining goLeft

  The transition function (phaseTransition) is defined by pattern matching on
  TMPhase, making proofs about each phase straightforward.

  For compatibility with TuringMachine.Machine (which uses Nat states),
  we define phaseToNat/natToPhase encoding. buildTransition dispatches through
  natToPhase → phaseTransition → phaseToNat.
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
-- TM phase type (proof-friendly state representation)
-- ============================================================================

inductive TMPhase where
  | halt
  | start
  | read (pos : Nat) (partialCode : Nat)
  | write (pos : Nat) (windowCode : Nat)
  | shift (remaining : Nat) (goLeft : Bool)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Nat state encoding (for TuringMachine.Machine compatibility)
-- ============================================================================

def nPow (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => n * nPow n k

def readState (params : GSParams) (pos : Nat) (partialCode : Nat) : Nat :=
  2 + pos * nPow params.alphabetSize params.windowWidth + partialCode

def writeStateBase (params : GSParams) : Nat :=
  2 + params.windowWidth * nPow params.alphabetSize params.windowWidth

def writeState (params : GSParams) (pos : Nat) (windowCode : Nat) : Nat :=
  writeStateBase params + pos * nPow params.alphabetSize params.windowWidth + windowCode

def shiftStateBase (params : GSParams) : Nat :=
  writeStateBase params + params.windowWidth * nPow params.alphabetSize params.windowWidth

def shiftState (params : GSParams) (remaining : Nat) (goLeft : Bool) : Nat :=
  shiftStateBase params + remaining * 2 + if goLeft then 1 else 0

def totalStates (params : GSParams) : Nat :=
  shiftStateBase params + (params.maxShift + 1) * 2

def phaseToNat (params : GSParams) : TMPhase → Nat
  | .halt => 0
  | .start => 1
  | .read pos partialCode => readState params pos partialCode
  | .write pos windowCode => writeState params pos windowCode
  | .shift remaining goLeft => shiftState params remaining goLeft

def natToPhase (params : GSParams) (state : Nat) : TMPhase :=
  if state = 0 then .halt
  else if state = 1 then .start
  else if state ≥ 2 && state < writeStateBase params then
    let offset := state - 2
    let nw := nPow params.alphabetSize params.windowWidth
    .read (offset / nw) (offset % nw)
  else if state ≥ writeStateBase params && state < shiftStateBase params then
    let offset := state - writeStateBase params
    let nw := nPow params.alphabetSize params.windowWidth
    .write (offset / nw) (offset % nw)
  else if state ≥ shiftStateBase params then
    let offset := state - shiftStateBase params
    .shift (offset / 2) (offset % 2 == 1)
  else .halt

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
-- Helpers
-- ============================================================================

def getListElem (list : List Nat) (idx : Nat) : Nat :=
  match list[idx]? with
  | some v => v
  | none => 0

-- ============================================================================
-- Phase transition function (clean, proof-friendly)
-- ============================================================================

private def startShiftPhase (params : GSParams) (repl : Nat)
    (rule : GeneralizedShift.ShiftRule) : TMPhase × Nat × Direction :=
  if rule.shiftMagnitude = 0 then
    (.start, repl, Direction.R)
  else if rule.shiftMagnitude = 1 then
    (.start, repl, if rule.shiftLeft then Direction.L else Direction.R)
  else
    (.shift (rule.shiftMagnitude - 2) rule.shiftLeft, repl,
     if rule.shiftLeft then Direction.L else Direction.R)

def phaseTransition (params : GSParams) (phase : TMPhase) (symbol : Nat) :
    TMPhase × Nat × Direction :=
  match phase with
  | .halt => (.halt, symbol, Direction.R)
  | .start =>
    if params.windowWidth ≤ 1 then
      let window := [symbol]
      if ¬ params.gsIsActive window then (.halt, symbol, Direction.R)
      else
        let rule := params.gsTransition window
        startShiftPhase params (getListElem rule.replacement 0) rule
    else (.read 1 symbol, symbol, Direction.R)
  | .read pos partialCode =>
    let newPartial := partialCode * params.alphabetSize + symbol
    if pos + 1 ≥ params.windowWidth then
      let window := decodeWindow params.alphabetSize params.windowWidth newPartial
      if ¬ params.gsIsActive window then (.halt, symbol, Direction.L)
      else
        let rule := params.gsTransition window
        let replHere := getListElem rule.replacement (params.windowWidth - 1)
        if params.windowWidth ≤ 1 then startShiftPhase params replHere rule
        else (.write (params.windowWidth - 2) newPartial, replHere, Direction.L)
    else (.read (pos + 1) newPartial, symbol, Direction.R)
  | .write pos windowCode =>
    let window := decodeWindow params.alphabetSize params.windowWidth windowCode
    let rule := params.gsTransition window
    let replHere := getListElem rule.replacement pos
    if pos = 0 then startShiftPhase params replHere rule
    else (.write (pos - 1) windowCode, replHere, Direction.L)
  | .shift remaining goLeft =>
    let dir := if goLeft then Direction.L else Direction.R
    if remaining = 0 then (.start, symbol, dir)
    else (.shift (remaining - 1) goLeft, symbol, dir)

-- ============================================================================
-- TM transition (Nat-encoded, dispatches through phaseTransition)
-- ============================================================================

def buildTransition (params : GSParams) (state : Nat) (symbol : Nat) : TransitionRule :=
  let (nextPhase, write, dir) := phaseTransition params (natToPhase params state) symbol
  { nextState := phaseToNat params nextPhase, write := write, direction := dir }

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
    (∀ w, params.gsIsActive w = true → (params.gsTransition w).shiftMagnitude ≥ 1) →
    GeneralizedShift.step (gsMachine params) gsConfig = some gsConfig' →
    ∃ n, n ≤ temporalOverhead params ∧
      BiInfiniteTuringMachine.exactSteps (toBiTM params) (encodeConfig gsConfig) n =
      some (encodeConfig gsConfig')

-- ============================================================================
-- Examples
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
-- natToPhase roundtrip for shift states
-- ============================================================================

private theorem natToPhase_shiftState (params : GSParams) (remaining : Nat) (goLeft : Bool) :
    natToPhase params (shiftState params remaining goLeft) = .shift remaining goLeft := by
  unfold natToPhase shiftState shiftStateBase writeStateBase
  generalize params.windowWidth * nPow params.alphabetSize params.windowWidth = A
  cases goLeft <;> simp <;>
    split <;> first | omega |
    (split <;> first | omega |
    (split <;> first | omega | rfl |
    (simp only [TMPhase.shift.injEq, beq_iff_eq]; omega)))

-- ============================================================================
-- Phase transition: shift phase is trivial by pattern matching
-- ============================================================================

theorem phaseTransition_shift (params : GSParams) (remaining : Nat) (goLeft : Bool) (symbol : Nat) :
    phaseTransition params (.shift remaining goLeft) symbol =
    (if remaining = 0 then .start else .shift (remaining - 1) goLeft,
     symbol,
     if goLeft then Direction.L else Direction.R) := by
  simp only [phaseTransition]; split <;> simp_all

-- ============================================================================
-- BiTM step from a shift-phase state
-- ============================================================================

private theorem buildTransition_shiftState (params : GSParams) (remaining : Nat)
    (goLeft : Bool) (symbol : Nat) :
    buildTransition params (shiftState params remaining goLeft) symbol =
    { nextState := if remaining = 0 then 1 else shiftState params (remaining - 1) goLeft,
      write := symbol,
      direction := if goLeft then Direction.L else Direction.R } := by
  simp only [buildTransition, natToPhase_shiftState, phaseTransition]
  split <;> simp_all [phaseToNat]

private theorem biTM_step_shiftState_right (params : GSParams) (remaining : Nat)
    (left : List Nat) (h : Nat) (right : List Nat) :
    BiInfiniteTuringMachine.step (toBiTM params)
      { state := shiftState params remaining false, left := left, head := h, right := right } =
    let nextSt := if remaining = 0 then 1 else shiftState params (remaining - 1) false
    let (newHead, newRight) := BiInfiniteTuringMachine.readHead right
    some { state := nextSt, left := h :: left, head := newHead, right := newRight } := by
  simp only [BiInfiniteTuringMachine.step, toBiTM]
  have hne : (shiftState params remaining false == 0) = false := by
    simp only [beq_eq_false_iff_ne]; unfold shiftState shiftStateBase writeStateBase; omega
  simp [hne, buildTransition_shiftState]

private theorem biTM_step_shiftState_left (params : GSParams) (remaining : Nat)
    (left : List Nat) (h : Nat) (right : List Nat) :
    BiInfiniteTuringMachine.step (toBiTM params)
      { state := shiftState params remaining true, left := left, head := h, right := right } =
    let nextSt := if remaining = 0 then 1 else shiftState params (remaining - 1) true
    let (newHead, newLeft) := BiInfiniteTuringMachine.readHead left
    some { state := nextSt, left := newLeft, head := newHead, right := h :: right } := by
  simp only [BiInfiniteTuringMachine.step, toBiTM]
  have hne : (shiftState params remaining true == 0) = false := by
    simp only [beq_eq_false_iff_ne]; unfold shiftState shiftStateBase writeStateBase; omega
  simp [hne, buildTransition_shiftState]

-- ============================================================================
-- Shift phase correctness (by induction on remaining)
-- ============================================================================

private theorem shiftPhase_right (params : GSParams) :
    ∀ (remaining : Nat) (left : List Nat) (h : Nat) (right : List Nat),
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := shiftState params remaining false, left := left, head := h, right := right }
      (remaining + 1) =
    some (encodeConfig (shiftBy { left := left, cells := [h], right := right }
      (remaining + 1) false)) := by
  intro remaining
  induction remaining with
  | zero =>
    intro left h right
    simp only [BiInfiniteTuringMachine.exactSteps, biTM_step_shiftState_right, ite_true,
      BiInfiniteTuringMachine.readHead]
    cases right with
    | nil => simp [shiftBy, GeneralizedShift.shiftRightOne, encodeConfig]
    | cons r rs => simp [shiftBy, GeneralizedShift.shiftRightOne, encodeConfig]
  | succ k ih =>
    intro left h right
    -- Unfold exactly one step of exactSteps (not recursively)
    unfold BiInfiniteTuringMachine.exactSteps
    -- Rewrite the step call, simplify match (some ...) and if conditions
    simp only [biTM_step_shiftState_right, show k + 1 ≠ 0 from by omega,
      ite_false, Nat.add_sub_cancel]
    cases right with
    | nil =>
      simp only [BiInfiniteTuringMachine.readHead]; rw [ih]
      simp [shiftBy, GeneralizedShift.shiftRightOne]
    | cons r rs =>
      simp only [BiInfiniteTuringMachine.readHead]; rw [ih]
      simp [shiftBy, GeneralizedShift.shiftRightOne]

private theorem shiftPhase_left (params : GSParams) :
    ∀ (remaining : Nat) (left : List Nat) (h : Nat) (right : List Nat),
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := shiftState params remaining true, left := left, head := h, right := right }
      (remaining + 1) =
    some (encodeConfig (shiftBy { left := left, cells := [h], right := right }
      (remaining + 1) true)) := by
  intro remaining
  induction remaining with
  | zero =>
    intro left h right
    simp only [BiInfiniteTuringMachine.exactSteps, biTM_step_shiftState_left, ite_true,
      BiInfiniteTuringMachine.readHead]
    cases left with
    | nil => simp [shiftBy, GeneralizedShift.shiftLeftOne, encodeConfig]
    | cons l ls => simp [shiftBy, GeneralizedShift.shiftLeftOne, encodeConfig]
  | succ k ih =>
    intro left h right
    unfold BiInfiniteTuringMachine.exactSteps
    simp only [biTM_step_shiftState_left, show k + 1 ≠ 0 from by omega,
      ite_false, Nat.add_sub_cancel]
    cases left with
    | nil =>
      simp only [BiInfiniteTuringMachine.readHead]; rw [ih]
      simp [shiftBy, GeneralizedShift.shiftLeftOne]
    | cons l ls =>
      simp only [BiInfiniteTuringMachine.readHead]; rw [ih]
      simp [shiftBy, GeneralizedShift.shiftLeftOne]

private theorem shiftPhase_correct (params : GSParams)
    (remaining : Nat) (goLeft : Bool) (left : List Nat) (h : Nat) (right : List Nat) :
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := shiftState params remaining goLeft, left := left, head := h, right := right }
      (remaining + 1) =
    some (encodeConfig (shiftBy { left := left, cells := [h], right := right }
      (remaining + 1) goLeft)) := by
  cases goLeft
  · exact shiftPhase_right params remaining left h right
  · exact shiftPhase_left params remaining left h right

-- ============================================================================
-- First TM step from state 1 (windowWidth = 1)
-- ============================================================================

private theorem natToPhase_one (params : GSParams) : natToPhase params 1 = .start := by
  unfold natToPhase; simp

-- First TM step from state 1, w=1, mag≥2: enters shift phase
private theorem biTM_step_start_w1_shift (params : GSParams) (c r : Nat)
    (hw : params.windowWidth = 1)
    (hActive : params.gsIsActive [c] = true)
    (hrep : (params.gsTransition [c]).replacement = [r])
    (hne0 : (params.gsTransition [c]).shiftMagnitude ≠ 0)
    (hne1 : (params.gsTransition [c]).shiftMagnitude ≠ 1)
    (left right : List Nat) :
    BiInfiniteTuringMachine.step (toBiTM params)
      { state := 1, left := left, head := c, right := right } =
    let dir := if (params.gsTransition [c]).shiftLeft then Direction.L else Direction.R
    match dir with
    | Direction.L =>
      let (newHead, newLeft) := readHead left
      some { state := shiftState params ((params.gsTransition [c]).shiftMagnitude - 2)
                (params.gsTransition [c]).shiftLeft,
             left := newLeft, head := newHead, right := r :: right }
    | Direction.R =>
      let (newHead, newRight) := readHead right
      some { state := shiftState params ((params.gsTransition [c]).shiftMagnitude - 2)
                (params.gsTransition [c]).shiftLeft,
             left := r :: left, head := newHead, right := newRight } := by
  simp only [BiInfiniteTuringMachine.step, toBiTM, buildTransition, natToPhase_one,
    phaseTransition, hw, Nat.le_refl, ite_true, hActive, not_true, ite_false,
    startShiftPhase, hrep, getListElem, phaseToNat, hne0, hne1]
  simp; rfl

-- For w=1: full simulation (first step from state 1 + shift phase)
private theorem fullSim_w1 (params : GSParams) (c r : Nat)
    (hw : params.windowWidth = 1)
    (hActive : params.gsIsActive [c] = true)
    (hrep : (params.gsTransition [c]).replacement = [r])
    (hMag : (params.gsTransition [c]).shiftMagnitude ≥ 1)
    (left right : List Nat) :
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := 1, left := left, head := c, right := right }
      (params.gsTransition [c]).shiftMagnitude =
    some (encodeConfig (shiftBy { left := left, cells := [r], right := right }
      (params.gsTransition [c]).shiftMagnitude (params.gsTransition [c]).shiftLeft)) := by
  -- mag ≥ 1, so write mag = (mag-1) + 1 to unfold one exactSteps
  -- Split on mag=1 vs mag≥2 first, then compute
  have hMag' : (params.gsTransition [c]).shiftMagnitude =
      ((params.gsTransition [c]).shiftMagnitude - 1) + 1 := by omega
  rw [hMag']; unfold BiInfiniteTuringMachine.exactSteps
  by_cases hM1 : (params.gsTransition [c]).shiftMagnitude = 1
  · -- mag = 1: one step, no shift phase
    rw [hM1]; simp only [show 1 - 1 = 0 from rfl, BiInfiniteTuringMachine.exactSteps,
      BiInfiniteTuringMachine.step, toBiTM, buildTransition, natToPhase_one,
      phaseTransition, hw, Nat.le_refl, ite_true, hActive, not_true, ite_false,
      startShiftPhase, hrep, getListElem, phaseToNat, hM1]
    cases (params.gsTransition [c]).shiftLeft <;>
      simp [shiftBy, GeneralizedShift.shiftRightOne, GeneralizedShift.shiftLeftOne,
            encodeConfig, readHead] <;> (first | (cases right <;> rfl) | (cases left <;> rfl))
  · -- mag ≥ 2: first step enters shift phase, then shiftPhase_correct
    have hne0 : (params.gsTransition [c]).shiftMagnitude ≠ 0 := by omega
    have hne1 : (params.gsTransition [c]).shiftMagnitude ≠ 1 := by omega
    -- Rewrite the step using the start lemma, then reduce let/match/if
    simp only [biTM_step_start_w1_shift params c r hw hActive hrep hne0 hne1]
    rw [show (params.gsTransition [c]).shiftMagnitude - 1 =
        (params.gsTransition [c]).shiftMagnitude - 2 + 1 from by omega]
    cases hDir : (params.gsTransition [c]).shiftLeft
    · cases right <;> (simp; rw [shiftPhase_correct]; congr 1)
    · cases left <;> (simp; rw [shiftPhase_correct]; congr 1)

-- ============================================================================
-- Step simulation proof for windowWidth = 1
-- ============================================================================

theorem stepSimulation_w1 (params : GSParams)
    (hw : params.windowWidth = 1)
    (hShift : ∀ w, params.gsIsActive w = true → (params.gsTransition w).shiftMagnitude ≥ 1)
    (hRepl : ∀ w, params.gsIsActive w = true →
      (params.gsTransition w).replacement.length = params.windowWidth)
    (hMaxShift : ∀ w, params.gsIsActive w = true →
      (params.gsTransition w).shiftMagnitude ≤ params.maxShift)
    (gsConfig gsConfig' : GeneralizedShift.Configuration)
    (hLen : gsConfig.cells.length = params.windowWidth)
    (hStep : GeneralizedShift.step (gsMachine params) gsConfig = some gsConfig') :
    ∃ n, n ≤ temporalOverhead params ∧
      BiInfiniteTuringMachine.exactSteps (toBiTM params) (encodeConfig gsConfig) n =
      some (encodeConfig gsConfig') := by
  rw [hw] at hLen
  obtain ⟨left, cells, right⟩ := gsConfig
  simp only at hLen hStep
  match hcells : cells with
  | [] => simp at hLen
  | [c] =>
    unfold GeneralizedShift.step gsMachine at hStep
    simp only at hStep
    by_cases hActive : params.gsIsActive [c] = true
    · simp only [hActive, not_true, ite_false] at hStep
      have hStep' := Option.some.inj hStep
      subst hStep'
      have hRL := hRepl [c] hActive; rw [hw] at hRL
      match hrep : (params.gsTransition [c]).replacement with
      | [] => rw [hrep] at hRL; simp at hRL
      | [r] =>
        have hMS := hMaxShift [c] hActive
        have hS := hShift [c] hActive
        refine ⟨(params.gsTransition [c]).shiftMagnitude, ?_, ?_⟩
        · unfold temporalOverhead; rw [hw]; omega
        · simp only [encodeConfig]
          exact fullSim_w1 params c r hw hActive hrep hS left right
      | _ :: _ :: _ => rw [hrep] at hRL; simp at hRL
    · rw [if_pos hActive] at hStep
      exact absurd hStep (by simp)
  | _ :: _ :: _ => simp at hLen

end GeneralizedShiftToTuringMachine
