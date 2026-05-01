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
import SimulationEncoding

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

private def startShiftPhase (_params : GSParams) (repl : Nat)
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
-- Arithmetic helpers
-- ============================================================================

private theorem nPow_pos (n : Nat) (hn : n ≥ 1) : ∀ k, nPow n k ≥ 1
  | 0 => by simp [nPow]
  | k + 1 => by
    unfold nPow
    have := nPow_pos n hn k
    calc n * nPow n k ≥ 1 * 1 := Nat.mul_le_mul hn this
    _ = 1 := by omega

private theorem nPow_pos' (params : GSParams) (hn : params.alphabetSize ≥ 1) :
    nPow params.alphabetSize params.windowWidth ≥ 1 :=
  nPow_pos _ hn _

private theorem succ_mul_eq (a b : Nat) : (a + 1) * b = a * b + b := by
  rw [Nat.add_mul, Nat.one_mul]

private theorem mul_nPow_lt (pos : Nat) (code : Nat) (w : Nat) (nw : Nat)
  (hPos : pos < w) (hCode : code < nw) (_hnw : nw ≥ 1) :
    pos * nw + code < w * nw := by
  have h1 : pos * nw + code < pos * nw + nw := by omega
  have h2 : pos * nw + nw = (pos + 1) * nw := (succ_mul_eq pos nw).symm
  have h3 : (pos + 1) * nw ≤ w * nw := Nat.mul_le_mul_right nw hPos
  omega

private theorem encodeWindow_bound (n : Nat) (hn : n ≥ 1) :
    ∀ (window : List Nat), (∀ x, x ∈ window → x < n) →
    encodeWindow n window < nPow n window.length
  | [], _ => by simp [encodeWindow, nPow]
  | x :: xs, hBound => by
    rw [encodeWindow_cons, List.length_cons, nPow]
    have hx : x < n := hBound x (List.Mem.head xs)
    have hxs := encodeWindow_bound n hn xs (fun y hy => hBound y (List.Mem.tail x hy))
    have hnp := nPow_pos n hn xs.length
    have h1 : encodeWindow n xs + x * nPow n xs.length
        < nPow n xs.length + x * nPow n xs.length := by omega
    have h2 : nPow n xs.length + x * nPow n xs.length = (x + 1) * nPow n xs.length :=
      by rw [succ_mul_eq]; omega
    have h3 : (x + 1) * nPow n xs.length ≤ n * nPow n xs.length :=
      Nat.mul_le_mul_right _ hx
    omega

private theorem exactSteps_none (machine : TuringMachine.Machine)
    (config : BiInfiniteTuringMachine.Configuration) (n : Nat)
    (h : BiInfiniteTuringMachine.step machine config = none) :
    BiInfiniteTuringMachine.exactSteps machine config (n + 1) = none := by
  cases n with
  | zero => simp [BiInfiniteTuringMachine.exactSteps, h]
  | succ k => simp [BiInfiniteTuringMachine.exactSteps, h]

private theorem exactSteps_succ (machine : TuringMachine.Machine)
    (config config' : BiInfiniteTuringMachine.Configuration) (n : Nat)
    (h : BiInfiniteTuringMachine.step machine config = some config') :
    BiInfiniteTuringMachine.exactSteps machine config (n + 1) =
    BiInfiniteTuringMachine.exactSteps machine config' n := by
  cases n with
  | zero => simp [BiInfiniteTuringMachine.exactSteps, h]
  | succ k => simp [BiInfiniteTuringMachine.exactSteps, h]

private theorem exactSteps_append (machine : TuringMachine.Machine)
    (c1 c2 : BiInfiniteTuringMachine.Configuration) (n1 n2 : Nat)
    (h : BiInfiniteTuringMachine.exactSteps machine c1 n1 = some c2) :
    BiInfiniteTuringMachine.exactSteps machine c1 (n1 + n2) =
    BiInfiniteTuringMachine.exactSteps machine c2 n2 := by
  induction n1 generalizing c1 with
  | zero => simp [BiInfiniteTuringMachine.exactSteps] at h; subst h; simp
  | succ k ih =>
    rw [show k + 1 + n2 = (k + n2) + 1 from by omega]
    simp only [BiInfiniteTuringMachine.exactSteps] at h ⊢
    match hStep : BiInfiniteTuringMachine.step machine c1 with
    | none => simp [hStep] at h
    | some c1' => simp only [hStep] at h ⊢; exact ih c1' h

-- ============================================================================
-- natToPhase roundtrips
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

private theorem natToPhase_readState (params : GSParams) (pos : Nat) (code : Nat)
    (hPos : pos < params.windowWidth)
    (hCode : code < nPow params.alphabetSize params.windowWidth) :
    natToPhase params (readState params pos code) = .read pos code := by
  unfold natToPhase readState writeStateBase
  generalize nPow params.alphabetSize params.windowWidth = nw at *
  have hnw : nw ≥ 1 := by omega
  have hlt : pos * nw + code < params.windowWidth * nw :=
    mul_nPow_lt pos code params.windowWidth nw hPos hCode hnw
  -- Navigate if/else: state = 2 + pos*nw + code, so ≠0, ≠1, in read range
  simp; split
  · omega
  · split
    · -- In read range ✓
      simp only [show 2 + pos * nw + code - 2 = pos * nw + code from by omega,
        TMPhase.read.injEq]
      exact ⟨mul_add_div_right pos code nw hnw (by omega),
             mul_add_mod_right pos code nw (by omega)⟩
    · -- Not in read range: hlt gives contradiction
      exfalso; omega

private theorem natToPhase_writeState (params : GSParams) (pos : Nat) (code : Nat)
    (hPos : pos < params.windowWidth)
    (hCode : code < nPow params.alphabetSize params.windowWidth) :
    natToPhase params (writeState params pos code) = .write pos code := by
  unfold natToPhase writeState writeStateBase shiftStateBase
  -- Unfold nPow and generalize so omega can handle all arithmetic
  generalize hNW : nPow params.alphabetSize params.windowWidth = nw at *
  have hnw : nw ≥ 1 := by omega
  have hlt : pos * nw + code < params.windowWidth * nw :=
    mul_nPow_lt pos code params.windowWidth nw hPos hCode hnw
  simp; split
  · omega
  · split
    · omega  -- In read range: contradiction (state ≥ 2 + w*nw > 2 + w*nw - 1)
    · split
      · -- In write range ✓
        have heq : 2 + params.windowWidth * nw + pos * nw + code - (2 + params.windowWidth * nw) =
            pos * nw + code := by omega
        rw [heq, mul_add_div_right pos code nw hnw (by omega),
            mul_add_mod_right pos code nw (by omega)]
      · -- Beyond write range: contradiction
        exfalso; unfold writeStateBase at *; rw [hNW] at *; omega

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
-- buildTransition characterization lemmas
-- ============================================================================

private theorem buildTransition_shiftState (params : GSParams) (remaining : Nat)
    (goLeft : Bool) (symbol : Nat) :
    buildTransition params (shiftState params remaining goLeft) symbol =
    { nextState := if remaining = 0 then 1 else shiftState params (remaining - 1) goLeft,
      write := symbol,
      direction := if goLeft then Direction.L else Direction.R } := by
  simp only [buildTransition, natToPhase_shiftState, phaseTransition]
  split <;> simp_all [phaseToNat]

private theorem buildTransition_readState (params : GSParams) (pos : Nat) (code : Nat)
    (symbol : Nat) (hPos : pos < params.windowWidth)
    (hCode : code < nPow params.alphabetSize params.windowWidth) :
    buildTransition params (readState params pos code) symbol =
    let (nextPhase, write, dir) :=
      phaseTransition params (.read pos code) symbol
    { nextState := phaseToNat params nextPhase, write := write, direction := dir } := by
  simp only [buildTransition, natToPhase_readState params pos code hPos hCode]

private theorem buildTransition_writeState (params : GSParams) (pos : Nat) (code : Nat)
    (symbol : Nat) (hPos : pos < params.windowWidth)
    (hCode : code < nPow params.alphabetSize params.windowWidth) :
    buildTransition params (writeState params pos code) symbol =
    let (nextPhase, write, dir) :=
      phaseTransition params (.write pos code) symbol
    { nextState := phaseToNat params nextPhase, write := write, direction := dir } := by
  simp only [buildTransition, natToPhase_writeState params pos code hPos hCode]

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

-- ============================================================================
-- Bridge: encodeConfig absorbs cells into head + right
-- ============================================================================

/-- encodeConfig flattens cells, so w-cell and 1-cell views of the same tape are equal. -/
private theorem encodeConfig_flatten (left : List Nat) (c : Nat) (cs right : List Nat) :
    encodeConfig { left := left, cells := c :: cs, right := right } =
    encodeConfig { left := left, cells := [c], right := cs ++ right } := by
  simp [encodeConfig]

/-- The key bridge: encodeConfig ∘ shiftBy only depends on the flat tape,
    not on where cells ends and right begins.
    Requires tape length ≥ mag to avoid 0-padding mismatch. -/
private theorem encodeConfig_shiftBy_right :
    ∀ (mag : Nat) (left : List Nat) (c : Nat) (cs right : List Nat),
    right.length ≥ mag →
    encodeConfig (shiftBy { left := left, cells := c :: cs, right := right } mag false) =
    encodeConfig (shiftBy { left := left, cells := [c], right := cs ++ right } mag false)
  | 0, left, c, cs, right, _ => encodeConfig_flatten left c cs right
  | mag + 1, left, c, cs, right, hLen => by
    unfold shiftBy; simp only [ite_false, Bool.false_eq_true]
    cases cs with
    | nil =>
      cases right with
      | nil => simp at hLen
      | cons r rs => simp [shiftRightOne, List.drop]
    | cons d ds =>
      cases right with
      | nil => simp at hLen
      | cons r rs =>
        simp only [shiftRightOne, List.drop]
        have hL : rs.length ≥ mag := by simp at hLen; omega
        have ih := encodeConfig_shiftBy_right mag (c :: left) d (ds ++ [r]) rs hL
        simp only [List.append_assoc] at ih; exact ih

private theorem encodeConfig_shiftBy_left :
    ∀ (mag : Nat) (left : List Nat) (c : Nat) (cs right : List Nat),
    left.length ≥ mag →
    encodeConfig (shiftBy { left := left, cells := c :: cs, right := right } mag true) =
    encodeConfig (shiftBy { left := left, cells := [c], right := cs ++ right } mag true)
  | 0, left, c, cs, right, _ => encodeConfig_flatten left c cs right
  | mag + 1, left, c, cs, right, hLen => by
    unfold shiftBy; simp only [ite_true]
    cases cs with
    | nil =>
      cases left with
      | nil => simp at hLen
      | cons l ls => simp [shiftLeftOne, List.getLastD, List.dropLast]
    | cons d ds =>
      cases left with
      | nil => simp at hLen
      | cons l ls =>
        -- After simp, the goal has c :: (d::ds).dropLast instead of (c::d::ds).dropLast
        -- and [c].getLast instead of c. Normalize before applying IH.
        simp only [shiftLeftOne, List.getLastD, List.dropLast, List.getLast]
        -- Now goal: ... l :: c :: (d::ds).dropLast ... = ... [l], c :: (d :: ds ++ right) ...
        -- IH needs cells = l :: (c :: d :: ds).dropLast = l :: c :: (d::ds).dropLast ✓
        have hL : ls.length ≥ mag := by simp at hLen; omega
        -- Rewrite (c::d::ds).dropLast to c :: (d::ds).dropLast in IH
        have hDL : (c :: d :: ds).dropLast = c :: (d :: ds).dropLast := by
          simp [List.dropLast]
        have hGL : (c :: d :: ds).getLast (by simp) = (d :: ds).getLast (by simp) := by
          simp [List.getLast]
        have ih := encodeConfig_shiftBy_left mag ls l ((c :: d :: ds).dropLast)
            ((c :: d :: ds).getLast (by simp) :: right) hL
        rw [hDL, hGL] at ih
        -- Need: shiftBy with right = (c :: dropLast) ++ (getLast :: right)
        --      = shiftBy with right = c :: d :: ds ++ right
        -- These lists are equal:
        have hList : (c :: (d :: ds).dropLast) ++ ((d :: ds).getLast (by simp) :: right) =
            c :: (d :: ds ++ right) := by
          rw [List.cons_append]
          congr 1
          have h1 := dropLast_append_getLast (show d :: ds ≠ [] from by simp)
          rw [show (d :: ds).getLast (by simp) :: right =
              [(d :: ds).getLast (by simp)] ++ right from rfl]
          rw [← List.append_assoc, h1]
        simp only [ih, hList]

private theorem encodeConfig_shiftBy_flatten (left : List Nat) (c : Nat) (cs right : List Nat)
    (mag : Nat) (dir : Bool)
    (hLen : if dir then left.length ≥ mag else right.length ≥ mag) :
    encodeConfig (shiftBy { left := left, cells := c :: cs, right := right } mag dir) =
    encodeConfig (shiftBy { left := left, cells := [c], right := cs ++ right } mag dir) := by
  cases dir
  · exact encodeConfig_shiftBy_right mag left c cs right (by simpa using hLen)
  · exact encodeConfig_shiftBy_left mag left c cs right (by simpa using hLen)


-- ============================================================================
-- Arithmetic helpers for code bounds
-- ============================================================================

private theorem nPow_mono (n : Nat) (hn : n ≥ 1) : ∀ {a b : Nat}, a ≤ b → nPow n a ≤ nPow n b := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (by simp [nPow]; exact Nat.le_mul_of_pos_left _ hn)

private theorem code_step_bound (n k : Nat) (code c : Nat)
    (hCode : code < nPow n k) (hC : c < n) (hn : n ≥ 1) :
    code * n + c < nPow n (k + 1) := by
  have hnn : 0 < n := by omega
  have step1 : code * n + c < (code + 1) * n := by rw [Nat.add_mul]; omega
  have step2 : (code + 1) * n ≤ nPow n k * n := Nat.mul_le_mul_right n hCode
  have step3 : nPow n k * n = nPow n (k + 1) := by simp [nPow, Nat.mul_comm]
  omega

-- ============================================================================
-- Read phase: start step + intermediate read loop
-- ============================================================================

/-- One start step from state 1 (w ≥ 2): reads c, writes c back, moves R. -/
private theorem biTM_step_start_w2 (params : GSParams) (hWidth : params.windowWidth ≥ 2)
    (left : List Nat) (c r : Nat) (right : List Nat) :
    BiInfiniteTuringMachine.step (toBiTM params)
      { state := 1, left := left, head := c, right := r :: right } =
    some { state := readState params 1 c, left := c :: left, head := r, right := right } := by
  simp only [BiInfiniteTuringMachine.step, toBiTM,
    show ((1 : Nat) == 0) = false from by decide, Bool.false_eq_true, ite_false,
    buildTransition, natToPhase_one, phaseTransition,
    show ¬(params.windowWidth ≤ 1) from by omega, ite_false, phaseToNat, readHead]

/-- One intermediate read step: reads c, writes c back, moves R. -/
private theorem biTM_step_readMid (params : GSParams) (_hAlpha : params.alphabetSize ≥ 1)
    (pos : Nat) (code c r : Nat) (left right : List Nat)
    (hPos : pos < params.windowWidth) (hNotLast : ¬(pos + 1 ≥ params.windowWidth))
    (hCode : code < nPow params.alphabetSize params.windowWidth) :
    BiInfiniteTuringMachine.step (toBiTM params)
      { state := readState params pos code, left := left, head := c, right := r :: right } =
    some { state := readState params (pos + 1) (code * params.alphabetSize + c),
           left := c :: left, head := r, right := right } := by
  simp only [BiInfiniteTuringMachine.step, toBiTM]
  have hne : (readState params pos code == 0) = false := by
    simp only [beq_eq_false_iff_ne]; unfold readState; omega
  simp only [hne, ite_false, buildTransition_readState params pos code c hPos hCode,
    phaseTransition, hNotLast, ite_false, phaseToNat, readHead]
  simp

/-- Read loop: from readState pos code, scan through cs then stop at last.
    Takes |cs| + 1 steps, accumulates code via foldl.
    Invariant: code < nPow n pos (tight bound, not nPow n w). -/
private theorem readMidLoop (params : GSParams) (hAlpha : params.alphabetSize ≥ 1) :
    ∀ (pos : Nat) (code c : Nat) (cs : List Nat) (last : Nat) (left right : List Nat),
    pos ≥ 1 →
    pos + cs.length + 1 < params.windowWidth →
    code < nPow params.alphabetSize pos →
    c < params.alphabetSize →
    (∀ x, x ∈ cs → x < params.alphabetSize) →
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := readState params pos code, left := left, head := c,
        right := cs ++ (last :: right) }
      (cs.length + 1) =
    some { state := readState params (pos + cs.length + 1)
             (List.foldl (fun acc v => acc * params.alphabetSize + v) code (c :: cs)),
           left := cs.reverse ++ (c :: left),
           head := last, right := right } := by
  intro pos code c cs
  induction cs generalizing pos code c with
  | nil =>
    intro last left right _ hPosLen hCode hC _
    simp only [List.length_nil, Nat.add_zero, List.nil_append, List.foldl_cons, List.foldl_nil,
      List.reverse_nil, List.nil_append]
    have hCodeW : code < nPow params.alphabetSize params.windowWidth :=
      Nat.lt_of_lt_of_le hCode (nPow_mono _ hAlpha (by omega))
    rw [show (0 + 1 : Nat) = 0 + 1 from rfl,
        exactSteps_succ _ _ _ _ (biTM_step_readMid params hAlpha pos code c last left right
          (by omega) (by omega) hCodeW)]
    simp [BiInfiniteTuringMachine.exactSteps]
  | cons d ds ih =>
    intro last left right hPos hPosLen hCode hC hBound
    have hD : d < params.alphabetSize := hBound d (List.Mem.head ds)
    have hDS : ∀ x, x ∈ ds → x < params.alphabetSize :=
      fun x hx => hBound x (List.Mem.tail d hx)
    simp only [List.length_cons, List.cons_append, List.reverse_cons]
    have hCodeNew : code * params.alphabetSize + c < nPow params.alphabetSize (pos + 1) :=
      code_step_bound _ _ code c hCode hC hAlpha
    have hCodeNewW : code * params.alphabetSize + c < nPow params.alphabetSize params.windowWidth :=
      Nat.lt_of_lt_of_le hCodeNew (nPow_mono _ hAlpha (by omega))
    have hCodeW : code < nPow params.alphabetSize params.windowWidth :=
      Nat.lt_of_lt_of_le hCode (nPow_mono _ hAlpha (by omega))
    -- Single step first (side condition), then IH for remaining steps
    have hSingleStep :
        BiInfiniteTuringMachine.exactSteps (toBiTM params)
          { state := readState params pos code, left := left, head := c,
            right := d :: (ds ++ last :: right) } 1 =
        some { state := readState params (pos + 1) (code * params.alphabetSize + c),
               left := c :: left, head := d, right := ds ++ last :: right } := by
      rw [show (1 : Nat) = 0 + 1 from rfl,
          exactSteps_succ _ _ _ _ (biTM_step_readMid params hAlpha pos code c d left
            (ds ++ last :: right) (by omega) (by omega) hCodeW)]
      simp [BiInfiniteTuringMachine.exactSteps]
    rw [show ds.length + 1 + 1 = 1 + (ds.length + 1) from by omega,
        exactSteps_append _ _ _ 1 _ hSingleStep]
    -- Now apply IH for remaining ds.length+1 steps
    have hGoal := ih (pos + 1) (code * params.alphabetSize + c) d last (c :: left) right
      (by omega) (by simp [List.length_cons] at hPosLen; omega) hCodeNew hD hDS
    simp only [show pos + 1 + ds.length + 1 = pos + (ds.length + 1) + 1 from by omega,
      show List.foldl (fun acc v => acc * params.alphabetSize + v) (code * params.alphabetSize + c) (d :: ds) =
           List.foldl (fun acc v => acc * params.alphabetSize + v) code (c :: d :: ds) from by
             simp [List.foldl_cons],
      show ds.reverse ++ d :: c :: left = ds.reverse ++ [d] ++ c :: left from by simp] at hGoal
    exact hGoal

/-- Combined read scan from state 1: start step + read loop.
    Scans cells c₀ :: cs, head ends at last. Takes |cs|+1 steps. -/
private theorem readScan (params : GSParams) (hAlpha : params.alphabetSize ≥ 1)
    (hWidth : params.windowWidth ≥ 2)
    (c₀ : Nat) (cs : List Nat) (last : Nat) (left right : List Nat)
    (hLen : cs.length + 2 ≤ params.windowWidth)
    (hC₀ : c₀ < params.alphabetSize)
    (hBound : ∀ x, x ∈ cs → x < params.alphabetSize) :
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := 1, left := left, head := c₀, right := cs ++ (last :: right) }
      (cs.length + 1) =
    some { state := readState params (cs.length + 1)
             (encodeWindow params.alphabetSize (c₀ :: cs)),
           left := cs.reverse ++ (c₀ :: left),
           head := last, right := right } := by
  cases cs with
  | nil =>
    simp only [List.length_nil, List.nil_append, List.reverse_nil, List.nil_append]
    rw [show (0 + 1 : Nat) = 0 + 1 from rfl,
        exactSteps_succ _ _ _ _ (biTM_step_start_w2 params hWidth left c₀ last right)]
    simp [BiInfiniteTuringMachine.exactSteps, encodeWindow_cons, encodeWindow_nil, nPow]
  | cons d ds =>
    simp only [List.length_cons]
    -- 1 start step + (ds.length + 1) read loop steps
    rw [show ds.length + 1 + 1 = 1 + (ds.length + 1) from by omega,
        exactSteps_append _ _
          { state := readState params 1 c₀, left := c₀ :: left,
            head := d, right := ds ++ (last :: right) } 1 _]
    · -- Read loop: apply readMidLoop with pos=1, code=c₀
      have hC₀Code : c₀ < nPow params.alphabetSize 1 := by simp [nPow]; exact hC₀
      have hDsBound : ∀ x, x ∈ ds → x < params.alphabetSize :=
        fun x hx => hBound x (List.Mem.tail d hx)
      have hD : d < params.alphabetSize := hBound d (List.Mem.head ds)
      have hGoal := readMidLoop params hAlpha 1 c₀ d ds last (c₀ :: left) right
        (by omega) (by simp [List.length_cons] at hLen; omega) hC₀Code hD hDsBound
      have hEnc : List.foldl (fun acc v => acc * params.alphabetSize + v) c₀ (d :: ds) =
          encodeWindow params.alphabetSize (c₀ :: d :: ds) := by simp [encodeWindow]
      have hLeft : ds.reverse ++ d :: c₀ :: left = (d :: ds).reverse ++ c₀ :: left := by
        simp [List.reverse_cons, List.append_assoc]
      simp only [show 1 + ds.length + 1 = 1 + (ds.length + 1) from by omega,
        hEnc, hLeft] at hGoal
      exact hGoal
    · -- Start step: normalize d :: ds ++ right = d :: (ds ++ right) then apply step lemma
      simp only [List.cons_append]
      rw [show (1 : Nat) = 0 + 1 from rfl,
          exactSteps_succ _ _ _ _ (biTM_step_start_w2 params hWidth left c₀ d
            (ds ++ last :: right))]
      simp [BiInfiniteTuringMachine.exactSteps]

-- ============================================================================
-- Write phase: last read + write loop + write-0
-- ============================================================================

/-- One intermediate write step: writes replacement[pos], moves L. -/
private theorem biTM_step_writeMid (params : GSParams) (_hAlpha : params.alphabetSize ≥ 1)
    (pos : Nat) (code : Nat) (head l : Nat) (left right : List Nat)
    (hPos : pos < params.windowWidth) (hPos1 : pos ≥ 1)
    (hCode : code < nPow params.alphabetSize params.windowWidth) :
    BiInfiniteTuringMachine.step (toBiTM params)
      { state := writeState params pos code, left := l :: left, head := head, right := right } =
    some { state := writeState params (pos - 1) code,
           left := left, head := l,
           right := getListElem (params.gsTransition
             (decodeWindow params.alphabetSize params.windowWidth code)).replacement pos
             :: right } := by
  simp only [BiInfiniteTuringMachine.step, toBiTM]
  have hne : (writeState params pos code == 0) = false := by
    simp only [beq_eq_false_iff_ne]; unfold writeState writeStateBase; omega
  simp only [hne, ite_false, buildTransition_writeState params pos code head hPos hCode,
    phaseTransition, show ¬(pos = 0) from by omega, ite_false, phaseToNat, readHead]
  simp

-- ============================================================================
-- Last read step: readState at pos = w-1, enters write phase
-- ============================================================================

/-- The last read step (cons form): from readState(w-1, partialCode) reading
    `last`, computes full window code, writes repl[w-1], moves L, enters
    writeState(w-2, code). The chain proof uses `chain_left_form` to rewrite
    `init.reverse ++ (c₀ :: origLeft)` into cons form before applying. -/
private theorem biTM_step_lastRead (params : GSParams) (hAlpha : params.alphabetSize ≥ 1)
    (hWidth : params.windowWidth ≥ 2)
    (partialCode last l : Nat) (left right : List Nat)
    (hPartial : partialCode < nPow params.alphabetSize (params.windowWidth - 1))
    (hActive : params.gsIsActive
      (decodeWindow params.alphabetSize params.windowWidth
        (partialCode * params.alphabetSize + last)) = true) :
    BiInfiniteTuringMachine.step (toBiTM params)
      { state := readState params (params.windowWidth - 1) partialCode,
        left := l :: left, head := last, right := right } =
    some { state := writeState params (params.windowWidth - 2)
             (partialCode * params.alphabetSize + last),
           left := left, head := l,
           right := getListElem (params.gsTransition
             (decodeWindow params.alphabetSize params.windowWidth
               (partialCode * params.alphabetSize + last))).replacement
             (params.windowWidth - 1) :: right } := by
  simp only [BiInfiniteTuringMachine.step, toBiTM]
  have hPosW : params.windowWidth - 1 < params.windowWidth := by omega
  have hCodeW : partialCode < nPow params.alphabetSize params.windowWidth :=
    Nat.lt_of_lt_of_le hPartial (nPow_mono _ hAlpha (by omega))
  have hne : (readState params (params.windowWidth - 1) partialCode == 0) = false := by
    simp only [beq_eq_false_iff_ne]; unfold readState; omega
  simp only [hne, ite_false,
    buildTransition_readState params (params.windowWidth - 1) partialCode last hPosW hCodeW,
    phaseTransition, show params.windowWidth - 1 + 1 ≥ params.windowWidth from by omega,
    ite_true, hActive, not_true, ite_false,
    show ¬(params.windowWidth ≤ 1) from by omega, phaseToNat, readHead]
  simp

-- ============================================================================
-- Write loop: k steps from writeState(k) down to writeState(0).
--
-- Uniform shape: k=0 is the no-op identity, k≥1 inducts. Lets the chain in
-- `fullSim_general_cView` handle w=2 and w≥3 uniformly (no case split).
-- ============================================================================

/-- replAsc repl k = [repl[1], repl[2], ..., repl[k]] (ascending index, k elements).
    Matches the right tape after k write steps (r_1 on top, r_k deepest). -/
private def replAsc (repl : List Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => replAsc repl k ++ [getListElem repl (k + 1)]

private theorem getLastD_cons (a : Nat) (l : List Nat) (d : Nat) :
    (a :: l).getLastD d = l.getLastD a := by
  cases l with
  | nil => rfl
  | cons b bs => simp [List.getLastD]

private theorem replAsc_succ_append (repl : List Nat) (k : Nat) (right : List Nat) :
    replAsc repl (k + 1) ++ right = replAsc repl k ++ (getListElem repl (k + 1) :: right) := by
  simp [replAsc, List.append_assoc]

/-- Write loop: from writeState(k, code) with `ls` (length k) atop the left
    tape, k steps reach writeState(0, code), popping `ls` from left and
    pushing `replAsc repl k` onto right. The k=0 case is the no-op identity. -/
private theorem writeLoop (params : GSParams) (hAlpha : params.alphabetSize ≥ 1)
    (code : Nat) (hCode : code < nPow params.alphabetSize params.windowWidth) :
    ∀ (k : Nat) (head : Nat) (ls : List Nat) (left₀ right : List Nat),
    ls.length = k →
    k < params.windowWidth →
    let repl := (params.gsTransition
      (decodeWindow params.alphabetSize params.windowWidth code)).replacement
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := writeState params k code,
        left := ls ++ left₀, head := head, right := right }
      k =
    some { state := writeState params 0 code,
           left := left₀, head := ls.getLastD head,
           right := replAsc repl k ++ right } := by
  intro k
  induction k with
  | zero =>
    intro head ls left₀ right hLen _hkW
    simp at hLen; subst hLen
    simp [BiInfiniteTuringMachine.exactSteps, replAsc, List.getLastD]
  | succ n ih =>
    intro head ls left₀ right hLen hkW
    match hls : ls with
    | [] => simp at hLen
    | l :: ls' =>
      simp only [List.length_cons] at hLen
      have hls'Len : ls'.length = n := by omega
      -- Single writeMid step: from writeState(n+1) peel l off left, push repl[n+1] onto right.
      have hStep : BiInfiniteTuringMachine.step (toBiTM params)
          { state := writeState params (n + 1) code,
            left := (l :: ls') ++ left₀, head := head, right := right } =
          some { state := writeState params n code,
                 left := ls' ++ left₀, head := l,
                 right := getListElem (params.gsTransition
                   (decodeWindow params.alphabetSize params.windowWidth code)).replacement (n + 1)
                   :: right } := by
        simp only [List.cons_append]
        rw [biTM_step_writeMid params hAlpha (n + 1) code head l (ls' ++ left₀) right
              (by omega) (by omega) hCode]
        simp [show n + 1 - 1 = n from by omega]
      -- Decompose n+1 steps as 1 + n via exactSteps_succ + IH.
      rw [exactSteps_succ _ _ _ _ hStep]
      -- IH for remaining n steps
      simp only at ih ⊢
      have hIH := ih l ls' left₀
            (getListElem (params.gsTransition
              (decodeWindow params.alphabetSize params.windowWidth code)).replacement (n + 1)
              :: right)
            hls'Len (by omega)
      rw [hIH, getLastD_cons, replAsc_succ_append]

-- ============================================================================
-- Write-zero + shift: from writeState(0), mag steps to final target
-- ============================================================================

/-- From writeState(0, fullCode), mag steps reach the shift target.
    Writes r₀ via startShiftPhase, then shifts. -/
private theorem writeZeroShift (params : GSParams) (_hAlpha : params.alphabetSize ≥ 1)
    (hWidth : params.windowWidth ≥ 2)
    (fullCode : Nat) (hCode : fullCode < nPow params.alphabetSize params.windowWidth)
    (cells : List Nat)
    (hDecode : decodeWindow params.alphabetSize params.windowWidth fullCode = cells)
  (_hActive : params.gsIsActive cells = true)
    (r₀ : Nat)
    (hR₀ : getListElem (params.gsTransition cells).replacement 0 = r₀)
    (hMag : (params.gsTransition cells).shiftMagnitude ≥ 1)
    (left : List Nat) (head : Nat) (right : List Nat) :
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      { state := writeState params 0 fullCode, left := left, head := head, right := right }
      (params.gsTransition cells).shiftMagnitude =
    some (encodeConfig (shiftBy { left := left, cells := [r₀], right := right }
      (params.gsTransition cells).shiftMagnitude
      (params.gsTransition cells).shiftLeft)) := by
  -- Split on direction first so each step proof gives `some {concrete config}`.
  have hW0ne : (writeState params 0 fullCode == 0) = false := by
    simp only [beq_eq_false_iff_ne]; unfold writeState writeStateBase; omega
  have hne0 : ¬((params.gsTransition cells).shiftMagnitude = 0) := by omega
  cases hDir : (params.gsTransition cells).shiftLeft
  · -- dir = false (shift right)
    by_cases hM1 : (params.gsTransition cells).shiftMagnitude = 1
    · -- mag = 1, R
      rw [hM1, show (1 : Nat) = 0 + 1 from rfl]
      have hStep : BiInfiniteTuringMachine.step (toBiTM params)
          { state := writeState params 0 fullCode, left := left, head := head, right := right } =
          some { state := 1, left := r₀ :: left,
                 head := (readHead right).1, right := (readHead right).2 } := by
        simp [BiInfiniteTuringMachine.step, toBiTM, hW0ne,
          buildTransition_writeState params 0 fullCode head (by omega) hCode,
          phaseTransition, hDecode, startShiftPhase, hM1, hDir, phaseToNat, hR₀, readHead]
      rw [exactSteps_succ _ _ _ _ hStep]; simp [BiInfiniteTuringMachine.exactSteps]
      cases right <;> simp [readHead, shiftBy, GeneralizedShift.shiftRightOne, encodeConfig]
    · -- mag ≥ 2, R
      rw [show (params.gsTransition cells).shiftMagnitude =
          ((params.gsTransition cells).shiftMagnitude - 2 + 1) + 1 from by omega]
      have hStep : BiInfiniteTuringMachine.step (toBiTM params)
          { state := writeState params 0 fullCode, left := left, head := head, right := right } =
          some { state := shiftState params ((params.gsTransition cells).shiftMagnitude - 2) false,
                 left := r₀ :: left,
                 head := (readHead right).1, right := (readHead right).2 } := by
        simp [BiInfiniteTuringMachine.step, toBiTM, hW0ne,
          buildTransition_writeState params 0 fullCode head (by omega) hCode,
          phaseTransition, hDecode, startShiftPhase, hne0, hM1, hDir, phaseToNat, hR₀, readHead]
      rw [exactSteps_succ _ _ _ _ hStep]
      cases right <;> (simp [readHead]; rw [shiftPhase_correct]; congr 1)
  · -- dir = true (shift left)
    by_cases hM1 : (params.gsTransition cells).shiftMagnitude = 1
    · -- mag = 1, L
      rw [hM1, show (1 : Nat) = 0 + 1 from rfl]
      have hStep : BiInfiniteTuringMachine.step (toBiTM params)
          { state := writeState params 0 fullCode, left := left, head := head, right := right } =
          some { state := 1, left := (readHead left).2,
                 head := (readHead left).1, right := r₀ :: right } := by
        simp [BiInfiniteTuringMachine.step, toBiTM, hW0ne,
          buildTransition_writeState params 0 fullCode head (by omega) hCode,
          phaseTransition, hDecode, startShiftPhase, hM1, hDir, phaseToNat, hR₀, readHead]
      rw [exactSteps_succ _ _ _ _ hStep]; simp [BiInfiniteTuringMachine.exactSteps]
      cases left <;> simp [readHead, shiftBy, GeneralizedShift.shiftLeftOne, encodeConfig]
    · -- mag ≥ 2, L
      rw [show (params.gsTransition cells).shiftMagnitude =
          ((params.gsTransition cells).shiftMagnitude - 2 + 1) + 1 from by omega]
      have hStep : BiInfiniteTuringMachine.step (toBiTM params)
          { state := writeState params 0 fullCode, left := left, head := head, right := right } =
          some { state := shiftState params ((params.gsTransition cells).shiftMagnitude - 2) true,
                 left := (readHead left).2,
                 head := (readHead left).1, right := r₀ :: right } := by
        simp [BiInfiniteTuringMachine.step, toBiTM, hW0ne,
          buildTransition_writeState params 0 fullCode head (by omega) hCode,
          phaseTransition, hDecode, startShiftPhase, hne0, hM1, hDir, phaseToNat, hR₀, readHead]
      rw [exactSteps_succ _ _ _ _ hStep]
      cases left <;> (simp [readHead]; rw [shiftPhase_correct]; congr 1)

-- ============================================================================
-- Chain helper lemmas for `fullSim_general_cView`
-- ============================================================================

/-- Bring a `init.reverse ++ (c₀ :: origLeft)` left tape into cons form, naming
    the head as `(c₀ :: init).getLast` and the tail as `(c₀ :: init).dropLast.reverse ++ origLeft`.
    Avoids case-splitting on `init` in the chain proof: handles `init = []` and
    `init = h :: t` uniformly. -/
private theorem chain_left_form (init : List Nat) (c₀ : Nat) (origLeft : List Nat) :
    init.reverse ++ (c₀ :: origLeft) =
    (c₀ :: init).getLast (List.cons_ne_nil c₀ init) ::
      ((c₀ :: init).dropLast.reverse ++ origLeft) := by
  have h_ne : (c₀ :: init) ≠ [] := List.cons_ne_nil c₀ init
  have h_split : (c₀ :: init).dropLast ++ [(c₀ :: init).getLast h_ne] = c₀ :: init :=
    dropLast_append_getLast h_ne
  -- Step 1: init.reverse ++ (c₀::origLeft) = (c₀::init).reverse ++ origLeft
  have h1 : init.reverse ++ (c₀ :: origLeft) = (c₀ :: init).reverse ++ origLeft := by
    show init.reverse ++ ([c₀] ++ origLeft) = _
    rw [← List.append_assoc]
    show (init.reverse ++ [c₀]) ++ origLeft = _
    rw [show init.reverse ++ [c₀] = (c₀ :: init).reverse from by rw [List.reverse_cons]]
  rw [h1]
  -- Step 2: (c₀::init).reverse = (c₀::init).getLast h_ne :: (c₀::init).dropLast.reverse
  have h2 : (c₀ :: init).reverse =
      (c₀ :: init).getLast h_ne :: (c₀ :: init).dropLast.reverse := by
    have hr := congrArg List.reverse h_split
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at hr
    exact hr.symm
  rw [h2]; rfl

/-- After writeLoop pops `(c₀::init).dropLast.reverse` from the left tape, the
    final head equals `c₀`. Holds uniformly: `init = []` (head = default) and
    `init = h :: t` (head = last element of non-empty list). -/
private theorem chain_getLastD (init : List Nat) (c₀ : Nat) :
    (c₀ :: init).dropLast.reverse.getLastD
        ((c₀ :: init).getLast (List.cons_ne_nil c₀ init)) = c₀ := by
  cases init with
  | nil => rfl
  | cons i₀ is =>
    show (c₀ :: (i₀ :: is).dropLast).reverse.getLastD _ = c₀
    rw [List.reverse_cons]
    exact List.getLastD_concat

-- ============================================================================
-- Full simulation for w ≥ 2 ([c]-view, no tape-length precondition).
--
-- Lands at the [c]-view (head=r₀, right=replAsc++right) — the natural shape of
-- the chain. The bridge to the multi-cell view (encodeConfig of the GS step)
-- is supplied separately by `decodeConfigPadded` for `SimulationEncoding`.
-- ============================================================================

/-- For w ≥ 2: 2(w-1) + mag TM steps from encodeConfig reach the [c]-view of the
    shift target — head = repl[0], right tape carries `replAsc repl (w-1)` then
    the original right tape. Symmetric to `fullSim_w1` (which uses [c]-view too,
    just without the read/write phases). -/
private theorem fullSim_general_cView (params : GSParams)
    (hAlpha : params.alphabetSize ≥ 1)
    (hWidth : params.windowWidth ≥ 2)
    (cells : List Nat) (repl : List Nat)
    (hLen : cells.length = params.windowWidth)
    (hActive : params.gsIsActive cells = true)
    (hCellBound : ∀ x, x ∈ cells → x < params.alphabetSize)
    (hRepl : (params.gsTransition cells).replacement = repl)
    (hReplLen : repl.length = params.windowWidth)
    (hMag : (params.gsTransition cells).shiftMagnitude ≥ 1)
    (left right : List Nat) :
    BiInfiniteTuringMachine.exactSteps (toBiTM params)
      (encodeConfig { left := left, cells := cells, right := right })
      (2 * (params.windowWidth - 1) + (params.gsTransition cells).shiftMagnitude) =
    some (encodeConfig (shiftBy
      { left := left,
        cells := [getListElem repl 0],
        right := replAsc repl (params.windowWidth - 1) ++ right }
      (params.gsTransition cells).shiftMagnitude
      (params.gsTransition cells).shiftLeft)) := by
  -- Decompose cells = c₀ :: tail (cells.length = w ≥ 2). The `match` substitutes
  -- `cells` to the matched pattern in both hypotheses and the goal.
  match hcells : cells with
  | [] => simp at hLen; omega
  | c₀ :: tail =>
    -- tail has length w-1, hence is non-empty. Split tail = init ++ [last].
    have htailLen : tail.length = params.windowWidth - 1 := by
      have := hLen; simp at this; omega
    have htailNe : tail ≠ [] := by
      intro h; rw [h] at htailLen; simp at htailLen; omega
    have hsplit : tail.dropLast ++ [tail.getLast htailNe] = tail :=
      dropLast_append_getLast htailNe
    have hinitLen : tail.dropLast.length = params.windowWidth - 2 := by
      rw [List.length_dropLast]; omega
    -- After the match, `cells` is substituted to `c₀ :: tail`. State the snoc
    -- form via `tail.dropLast ++ [tail.getLast htailNe] = tail`.
    have hcells_split : (c₀ :: tail) = c₀ :: tail.dropLast ++ [tail.getLast htailNe] := by
      rw [show c₀ :: tail.dropLast ++ [tail.getLast htailNe] =
            c₀ :: (tail.dropLast ++ [tail.getLast htailNe]) from rfl, hsplit]
    have hRightForm : tail ++ right = tail.dropLast ++ (tail.getLast htailNe :: right) := by
      rw [show tail.dropLast ++ (tail.getLast htailNe :: right)
            = (tail.dropLast ++ [tail.getLast htailNe]) ++ right from by simp, hsplit]
    -- Cell bounds: c₀, init, last all < alphabetSize. `hCellBound` already has
    -- `cells` substituted to `c₀ :: tail`.
    have hC₀ : c₀ < params.alphabetSize := hCellBound c₀ (List.Mem.head _)
    have hCInit : ∀ x, x ∈ tail.dropLast → x < params.alphabetSize := fun x hx => by
      apply hCellBound
      rw [hcells_split]
      exact List.Mem.tail c₀ (List.mem_append_left _ hx)
    have hLast : tail.getLast htailNe < params.alphabetSize := by
      apply hCellBound
      rw [hcells_split]
      exact List.Mem.tail c₀ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    -- code = encodeWindow (c₀ :: init); fullCode = code * α + last; both bounded.
    have hWinLen : (c₀ :: tail.dropLast).length = params.windowWidth - 1 := by
      simp [List.length_cons]; omega
    have hWinBound : ∀ x, x ∈ (c₀ :: tail.dropLast) → x < params.alphabetSize := by
      intro x hx
      cases hx with
      | head => exact hC₀
      | tail _ hxin => exact hCInit x hxin
    have hCode : encodeWindow params.alphabetSize (c₀ :: tail.dropLast) <
                  nPow params.alphabetSize (params.windowWidth - 1) := by
      have := encodeWindow_bound params.alphabetSize hAlpha (c₀ :: tail.dropLast) hWinBound
      rw [hWinLen] at this; exact this
    -- Decode the full window code back to `cells` (needed for writeZeroShift's
    -- `hDecode` precondition, which references the cells via decodeWindow).
    have hDecodeFull : decodeWindow params.alphabetSize params.windowWidth
        (encodeWindow params.alphabetSize (c₀ :: tail.dropLast) * params.alphabetSize +
          tail.getLast htailNe) = c₀ :: tail := by
      have hWinLen2 : ((c₀ :: tail.dropLast) ++ [tail.getLast htailNe]).length =
          params.windowWidth := by simp; omega
      have hWinBound2 : ∀ x, x ∈ ((c₀ :: tail.dropLast) ++ [tail.getLast htailNe]) →
          x < params.alphabetSize := by
        intro x hx
        rcases List.mem_append.mp hx with hl | hr
        · exact hWinBound x hl
        · rw [List.mem_singleton] at hr; rw [hr]; exact hLast
      have h := decodeWindow_encodeWindow params.alphabetSize params.windowWidth
        ((c₀ :: tail.dropLast) ++ [tail.getLast htailNe]) hWinLen2 hWinBound2 (by omega)
      rw [encodeWindow_snoc] at h
      rw [h]; exact hcells_split.symm
    -- ============== Phase 1 (readScan): w-1 steps ==============
    have hReadScanLen : tail.dropLast.length + 2 ≤ params.windowWidth := by omega
    have hReadScan := readScan params hAlpha hWidth c₀ tail.dropLast (tail.getLast htailNe)
        left right hReadScanLen hC₀ hCInit
    -- Setup encodeConfig: state in terms of c₀::tail (matches the substituted goal).
    have hEncode : encodeConfig { left := left, cells := c₀ :: tail, right := right } =
        { state := 1, left := left, head := c₀, right := tail ++ right } := rfl
    rw [hEncode, hRightForm]
    -- Decompose 2(w-1)+mag = (w-1) + ((w-2 + mag) + 1) so the final `+1` lets
    -- `exactSteps_succ` apply for the lastRead step (which moves L by 1).
    rw [show 2 * (params.windowWidth - 1) + (params.gsTransition (c₀ :: tail)).shiftMagnitude
            = (tail.dropLast.length + 1) +
              ((tail.dropLast.length + (params.gsTransition (c₀ :: tail)).shiftMagnitude) + 1)
            from by omega]
    rw [exactSteps_append _ _ _ (tail.dropLast.length + 1) _ hReadScan]
    -- ============== Phase 2 (lastRead): 1 step ==============
    have hStep1Eq : tail.dropLast.length + 1 = params.windowWidth - 1 := by omega
    have hActiveFull : params.gsIsActive
        (decodeWindow params.alphabetSize params.windowWidth
          (encodeWindow params.alphabetSize (c₀ :: tail.dropLast) * params.alphabetSize +
            tail.getLast htailNe)) = true := by
      rw [hDecodeFull]; exact hActive
    -- Rewrite goal's left (output of readScan) into cons form via chain_left_form.
    rw [chain_left_form tail.dropLast c₀ left]
    -- Rewrite goal's state w-1+1 → w-1 so it matches biTM_step_lastRead's signature.
    rw [hStep1Eq]
    -- Apply biTM_step_lastRead in cons form
    have hLastReadStep := biTM_step_lastRead params hAlpha hWidth
        (encodeWindow params.alphabetSize (c₀ :: tail.dropLast)) (tail.getLast htailNe)
        ((c₀ :: tail.dropLast).getLast (List.cons_ne_nil c₀ tail.dropLast))
        ((c₀ :: tail.dropLast).dropLast.reverse ++ left) right hCode hActiveFull
    rw [exactSteps_succ _ _ _ _ hLastReadStep]
    -- ============== Phase 3 (writeLoop with k = w-2): w-2 steps ==============
    -- writeLoop input state = writeState(k) where k = tail.dropLast.length = w-2.
    have hWriteLoopLs : (c₀ :: tail.dropLast).dropLast.reverse.length = tail.dropLast.length := by
      rw [List.length_reverse, List.length_dropLast]
      simp [List.length_cons]
    have hCodeFull : encodeWindow params.alphabetSize (c₀ :: tail.dropLast) *
        params.alphabetSize + tail.getLast htailNe <
        nPow params.alphabetSize params.windowWidth := by
      have := code_step_bound params.alphabetSize (params.windowWidth - 1)
        (encodeWindow params.alphabetSize (c₀ :: tail.dropLast)) (tail.getLast htailNe)
        hCode hLast hAlpha
      rw [show params.windowWidth - 1 + 1 = params.windowWidth from by omega] at this
      exact this
    have hWriteLoop := writeLoop params hAlpha
        (encodeWindow params.alphabetSize (c₀ :: tail.dropLast) *
          params.alphabetSize + tail.getLast htailNe)
        hCodeFull tail.dropLast.length
        ((c₀ :: tail.dropLast).getLast (List.cons_ne_nil c₀ tail.dropLast))
        (c₀ :: tail.dropLast).dropLast.reverse left
        (getListElem (params.gsTransition
          (decodeWindow params.alphabetSize params.windowWidth
            (encodeWindow params.alphabetSize (c₀ :: tail.dropLast) *
              params.alphabetSize + tail.getLast htailNe))).replacement
          (params.windowWidth - 1) :: right)
        hWriteLoopLs (by omega)
    -- lastRead output state is writeState(w-2). Bridge: w-2 = tail.dropLast.length.
    rw [show params.windowWidth - 2 = tail.dropLast.length from by omega]
    rw [exactSteps_append _ _ _ tail.dropLast.length _ hWriteLoop]
    -- ============== Phase 4 (writeZeroShift): mag steps ==============
    -- Simplify head via chain_getLastD; bridge right via replAsc_succ_append.
    rw [chain_getLastD tail.dropLast c₀]
    -- Replace internal `gsTransition (decodeWindow ...)` with `gsTransition (c₀ :: tail)` via hDecodeFull.
    -- Then `(params.gsTransition (c₀ :: tail)).replacement = repl` via hRepl.
    have hReplBridge : (params.gsTransition
        (decodeWindow params.alphabetSize params.windowWidth
          (encodeWindow params.alphabetSize (c₀ :: tail.dropLast) *
            params.alphabetSize + tail.getLast htailNe))).replacement = repl := by
      rw [hDecodeFull]; exact hRepl
    rw [hReplBridge]
    -- replAsc bridge: with k = tail.dropLast.length = w-2,
    -- replAsc repl (w-1) ++ right = replAsc repl (w-2) ++ (repl[w-1] :: right)
    rw [show params.windowWidth - 1 = tail.dropLast.length + 1 from by omega]
    rw [replAsc_succ_append]
    -- Apply writeZeroShift for mag steps. Output: encodeConfig of shiftBy of [r₀]-view.
    have hWriteZeroShift := writeZeroShift params hAlpha hWidth
      (encodeWindow params.alphabetSize (c₀ :: tail.dropLast) *
        params.alphabetSize + tail.getLast htailNe)
      hCodeFull (c₀ :: tail) hDecodeFull hActive
      (getListElem repl 0)
      (by rw [hRepl])
      hMag left c₀ (replAsc repl tail.dropLast.length ++
        (getListElem repl (tail.dropLast.length + 1) :: right))
    exact hWriteZeroShift

-- ============================================================================
-- decodeConfigPadded: decode a TM config back to a GS config with cells.length
-- = windowWidth, padding the cells with 0 if the right tape is shorter than
-- (windowWidth - 1). Symmetric to TM→GS direction's normalized BiTM step
-- (which post-strips trailing zeros): here we pad on decode rather than strip.
-- ============================================================================

def decodeConfigPadded (windowWidth : Nat) (tmConfig : BiInfiniteTuringMachine.Configuration)
    : Option GeneralizedShift.Configuration :=
  if tmConfig.state ≠ 1 then none
  else
    let prfx := tmConfig.right.take (windowWidth - 1)
    let pad := List.replicate (windowWidth - 1 - prfx.length) 0
    some { left := tmConfig.left,
           cells := tmConfig.head :: (prfx ++ pad),
           right := tmConfig.right.drop (windowWidth - 1) }

/-- Static bridge: padded decode of encoded config recovers original cells,
    when cells.length = w. -/
private theorem decodeConfigPadded_encodeConfig
    (w : Nat) (gsConfig : GeneralizedShift.Configuration)
    (hLen : gsConfig.cells.length = w) (hw : w ≥ 1) :
    decodeConfigPadded w (encodeConfig gsConfig) = some gsConfig := by
  cases hc : gsConfig.cells with
  | nil => rw [hc] at hLen; simp at hLen; omega
  | cons c cs =>
    simp only [encodeConfig, hc, decodeConfigPadded]
    rw [hc] at hLen; simp only [List.length] at hLen
    have hCsLen : cs.length = w - 1 := by omega
    have hTake : (cs ++ gsConfig.right).take (w - 1) = cs := List.take_left' hCsLen
    have hDrop : (cs ++ gsConfig.right).drop (w - 1) = gsConfig.right := List.drop_left' hCsLen
    rw [hTake, hDrop, hCsLen, Nat.sub_self]
    simp [List.replicate]
    obtain ⟨left, _, right⟩ := gsConfig
    simp only at hc; subst hc
    rfl

-- ============================================================================
-- Per-step bridge: decodeConfigPadded ∘ encodeConfig commutes with `shift{Left,Right}One`.
--
-- For X with X.cells = [c] (single cell, [c]-view), one shift in the [c]-view
-- followed by decode equals decode followed by one shift in the multi-cell view.
-- The padding inside `decodeConfigPadded` reconciles the syntactic differences
-- (trailing 0s) that arise when the tape is shorter than w-1 on the shift side.
-- ============================================================================

/-- Helper: shiftRightOne on a [c]-view config, right-tape empty case. -/
private theorem shiftRightOne_singleton_nil (left : List Nat) (c : Nat) :
    GeneralizedShift.shiftRightOne { left := left, cells := [c], right := [] } =
    { left := c :: left, cells := [0], right := [] } := rfl

/-- Helper: shiftRightOne on a [c]-view config, right-tape cons case. -/
private theorem shiftRightOne_singleton_cons (left rs : List Nat) (c r : Nat) :
    GeneralizedShift.shiftRightOne { left := left, cells := [c], right := r :: rs } =
    { left := c :: left, cells := [r], right := rs } := rfl

/-- Helper: shiftRightOne on a (c :: cs)-view config, right-tape empty case. -/
private theorem shiftRightOne_cons_nil (left cs : List Nat) (c : Nat) :
    GeneralizedShift.shiftRightOne { left := left, cells := c :: cs, right := [] } =
    { left := c :: left, cells := cs ++ [0], right := [] } := rfl

/-- Helper: shiftRightOne on a (c :: cs)-view config, right-tape cons case. -/
private theorem shiftRightOne_cons_cons (left cs rs : List Nat) (c r : Nat) :
    GeneralizedShift.shiftRightOne { left := left, cells := c :: cs, right := r :: rs } =
    { left := c :: left, cells := cs ++ [r], right := rs } := rfl

/-- Helper: shiftLeftOne on a [c]-view config, left-tape empty case. -/
private theorem shiftLeftOne_singleton_nil (right : List Nat) (c : Nat) :
    GeneralizedShift.shiftLeftOne { left := [], cells := [c], right := right } =
    { left := [], cells := [0], right := c :: right } := rfl

/-- Helper: shiftLeftOne on a [c]-view config, left-tape cons case. -/
private theorem shiftLeftOne_singleton_cons (ls right : List Nat) (l c : Nat) :
    GeneralizedShift.shiftLeftOne { left := l :: ls, cells := [c], right := right } =
    { left := ls, cells := [l], right := c :: right } := rfl

/-- Helper: shiftLeftOne on a multi-cell config (cells = c :: cs), left-tape empty.
    Reduces by `rfl` because the structure is concrete. -/
private theorem shiftLeftOne_cons_nil (cs right : List Nat) (c : Nat) :
    GeneralizedShift.shiftLeftOne { left := [], cells := c :: cs, right := right } =
    { left := [], cells := 0 :: (c :: cs).dropLast,
      right := (c :: cs).getLastD 0 :: right } := rfl

/-- Helper: shiftLeftOne on a multi-cell config (cells = c :: cs), left-tape cons.
    Reduces by `rfl` because the structure is concrete. -/
private theorem shiftLeftOne_cons_cons (ls right cs : List Nat) (l c : Nat) :
    GeneralizedShift.shiftLeftOne { left := l :: ls, cells := c :: cs, right := right } =
    { left := ls, cells := l :: (c :: cs).dropLast,
      right := (c :: cs).getLastD 0 :: right } := rfl

/-- Helper: encodeConfig on a [c]-view config. -/
private theorem encodeConfig_singleton (left right : List Nat) (c : Nat) :
    encodeConfig { left := left, cells := [c], right := right } =
    { state := 1, left := left, head := c, right := right } := by
  simp [encodeConfig]

/-- Helper: decodeConfigPadded on a state=1 TM config in computed form. -/
private theorem decodeConfigPadded_state1
    (w : Nat) (left right : List Nat) (head : Nat) :
    decodeConfigPadded w
        { state := 1, left := left, head := head, right := right } =
      some { left := left,
             cells := head :: (right.take (w - 1)
                ++ List.replicate (w - 1 - (right.take (w - 1)).length) 0),
             right := right.drop (w - 1) } := by
  simp [decodeConfigPadded]

/-- Helper: when `right.length ≥ w-1`, the padding is empty so decodePadded
    reduces to the simple "no padding" form. -/
private theorem decodePadded_proper_form (w : Nat)
    (left right : List Nat) (head : Nat) (hLen : right.length ≥ w - 1) :
    decodeConfigPadded w
        { state := 1, left := left, head := head, right := right } =
      some { left := left,
             cells := head :: right.take (w - 1),
             right := right.drop (w - 1) } := by
  rw [decodeConfigPadded_state1]
  have hTakeLen : (right.take (w - 1)).length = w - 1 := by
    rw [List.length_take]; omega
  rw [hTakeLen, Nat.sub_self]
  simp [List.replicate]

/-- Per-step bridge for shiftRightOne. One shift in [c]-view followed by decode
    equals decode followed by one shift in multi-cell view. List-arithmetic case
    analysis on `right` and on whether `|right| ≥ w-1`, handling the [0]-padding
    from short tapes. -/
private theorem decodePadded_shiftRightOne (w : Nat) (hw : w ≥ 1)
    (left right : List Nat) (c : Nat) :
    decodeConfigPadded w (encodeConfig
      (GeneralizedShift.shiftRightOne { left := left, cells := [c], right := right })) =
    (decodeConfigPadded w (encodeConfig
      { left := left, cells := [c], right := right })).map GeneralizedShift.shiftRightOne := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  -- Throughout: w - 1 = k, w = k + 1.
  cases right with
  | nil =>
    -- Both sides reduce to some {c::left, replicate (k+1) 0, []}.
    rw [shiftRightOne_singleton_nil, encodeConfig_singleton,
        encodeConfig_singleton, decodeConfigPadded_state1, decodeConfigPadded_state1]
    simp only [List.take_nil, List.drop_nil, List.length_nil, Nat.sub_zero,
               Option.map_some]
    congr 1
    -- Goal: cell-eq: {c::left, 0::replicate k 0, []} = shiftRightOne {left, c::replicate k 0, []}
    show ({ left := c :: left, cells := 0 :: List.replicate k 0, right := [] }
            : GeneralizedShift.Configuration) =
         GeneralizedShift.shiftRightOne
           { left := left, cells := c :: List.replicate k 0, right := [] }
    -- Compute shiftRightOne on the right
    -- cells = c :: replicate k 0 → newLeft = c :: left, tail = replicate k 0
    -- right = [] → cells_new = replicate k 0 ++ [0]
    show _ = ({ left := c :: left, cells := List.replicate k 0 ++ [0], right := [] }
              : GeneralizedShift.Configuration)
    congr 1
    -- 0 :: replicate k 0 = replicate k 0 ++ [0]
    rw [show (0 :: List.replicate k 0) = List.replicate (k + 1) 0 from rfl,
        List.replicate_succ']
  | cons r rs =>
    -- LHS: shiftRightOne {left, [c], r::rs} = {c::left, [r], rs}
    --       encode → {1, c::left, r, rs}, decodePadded → some {c::left, r :: (rs.take k ++ pad), rs.drop k}
    --       where pad = replicate (k - rs.take k.length) 0.
    -- RHS: encode → {1, left, c, r::rs}, decodePadded → some {left, c :: ((r::rs).take k ++ pad'), (r::rs).drop k}
    --       where pad' = replicate (k - (r::rs).take k.length) 0.
    --       Then shiftRightOne {left, c :: ..., (r::rs).drop k}:
    --         newLeft = c :: left, tail = (r::rs).take k ++ pad'
    --         match (r::rs).drop k: case-split.
    rw [shiftRightOne_singleton_cons, encodeConfig_singleton,
        encodeConfig_singleton, decodeConfigPadded_state1, decodeConfigPadded_state1]
    simp only [Option.map_some]
    cases k with
    | zero =>
      -- w = 1: [c]-view = multi-cell view; trivial.
      simp only [Nat.add_sub_cancel, List.take_zero, List.drop_zero,
                 List.length_nil, Nat.sub_zero, List.replicate, List.append_nil]
      rfl
    | succ k' =>
      -- w ≥ 2.
      simp only [Nat.add_sub_cancel, List.take_succ_cons, List.drop_succ_cons,
                 List.length_cons]
      -- Now unfold the outer shiftRightOne on the RHS
      -- cells_RHS_input = c :: (r :: rs.take k' ++ pad')
      -- where pad' = replicate (k' + 1 - (r :: rs.take k').length) 0
      --             = replicate (k' + 1 - (1 + rs.take k'.length)) 0
      --             = replicate (k' - rs.take k'.length) 0
      -- Need to reduce shiftRightOne. The cells_RHS_input is `c :: ...`, so newLeft = c :: left,
      -- tail = r :: rs.take k' ++ pad'.
      -- The right field is rs.drop k'. Case split.
      cases hrs : rs.drop k' with
      | nil =>
        -- rs.length ≤ k'.
        have hRsLen : rs.length ≤ k' := List.drop_eq_nil_iff.mp hrs
        rw [List.take_of_length_le hRsLen,
            List.take_of_length_le (by omega : rs.length ≤ k' + 1),
            List.drop_of_length_le (by omega : rs.length ≤ k' + 1),
            shiftRightOne_cons_nil]
        -- Goal: some {c::left, r :: (rs ++ replicate (k'+1-rs.length) 0), []} =
        --       some {c::left, (r :: rs ++ replicate (k'+1-(rs.length+1)) 0) ++ [0], []}
        congr 2
        -- Goal: r :: (rs ++ replicate (k'+1-rs.length) 0) =
        --       (r :: rs ++ replicate (k'+1-(rs.length+1)) 0) ++ [0]
        rw [show k' + 1 - rs.length = (k' - rs.length) + 1 from by omega,
            show k' + 1 - (rs.length + 1) = k' - rs.length from by omega,
            List.replicate_succ']
        simp [List.append_assoc]
      | cons r' rs' =>
        -- rs.length ≥ k' + 1.
        have hRsDrop : rs.drop k' ≠ [] := by rw [hrs]; exact List.cons_ne_nil _ _
        have hRsLenGT : k' < rs.length := by
          rcases Nat.lt_or_ge k' rs.length with h | h
          · exact h
          · exact absurd (List.drop_of_length_le h) hRsDrop
        have hTakeK' : (rs.take k').length = k' := by
          rw [List.length_take]; omega
        -- rs[k'] = r' (from hrs).
        have hGet : rs[k']'hRsLenGT = r' := by
          have := List.drop_eq_getElem_cons (l := rs) (i := k') hRsLenGT
          rw [hrs] at this
          exact ((List.cons.injEq _ _ _ _).mp this |>.1).symm
        -- rs.take (k'+1) = rs.take k' ++ [r']
        have hTakeKK : rs.take (k' + 1) = rs.take k' ++ [r'] := by
          rw [List.take_succ_eq_append_getElem hRsLenGT, hGet]
        -- rs.drop (k'+1) = rs'
        have hDropKK : rs.drop (k' + 1) = rs' := by
          have := List.drop_eq_getElem_cons (l := rs) (i := k') hRsLenGT
          rw [hrs, hGet] at this
          exact (List.cons.injEq _ _ _ _).mp this.symm |>.2
        rw [hTakeKK, hDropKK, shiftRightOne_cons_cons]
        -- Goal: some {c::left, r :: (rs.take k' ++ [r'] ++ replicate (k'+1 - (rs.take k' ++ [r']).length) 0), rs'} =
        --       some {c::left, (r :: rs.take k' ++ replicate (k'+1 - (rs.take k'.length+1)) 0) ++ [r'], rs'}
        rw [show ((rs.take k' ++ [r']).length) = k' + 1 from by simp [hTakeK']]
        rw [Nat.sub_self, hTakeK']
        rw [show k' + 1 - (k' + 1) = 0 from by omega]
        simp [List.replicate]

/-- Per-step bridge for shiftLeftOne. Requires `right.length ≥ w - 1` because
    multi-cell shiftLeft pushes the rightmost cell (which may be a padding 0
    when the right tape is short) onto the right tape, while [c]-view shiftLeft
    pushes the original `c`. The two only agree when there is no padding —
    equivalent to `right.length ≥ w - 1`. The precondition is preserved by
    shiftLeft (which only grows the right tape), so it propagates through the
    `shiftBy mag true` induction. -/
private theorem decodePadded_shiftLeftOne (w : Nat) (hw : w ≥ 1)
    (left right : List Nat) (c : Nat) (hRightLen : right.length ≥ w - 1) :
    decodeConfigPadded w (encodeConfig
      (GeneralizedShift.shiftLeftOne { left := left, cells := [c], right := right })) =
    (decodeConfigPadded w (encodeConfig
      { left := left, cells := [c], right := right })).map GeneralizedShift.shiftLeftOne := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hRightLen
  -- The key insight: with hRightLen, both sides reduce to the same explicit form
  -- via `decodePadded_proper_form`.
  -- LHS path: shiftLeft cView produces a [c]-view with new right tape = c :: right
  --   (length = right.length + 1 ≥ k + 1 ≥ k). Apply `decodePadded_proper_form`.
  -- RHS path: decodePadded original gives multi-cell view (using `decodePadded_proper_form`).
  --   Then apply shiftLeft_multi.
  cases left with
  | nil =>
    rw [shiftLeftOne_singleton_nil, encodeConfig_singleton, encodeConfig_singleton]
    rw [decodePadded_proper_form (k + 1) [] (c :: right) 0
          (by simp; omega),
        decodePadded_proper_form (k + 1) [] right c
          (by simp; omega)]
    simp only [Option.map_some, Nat.add_sub_cancel]
    cases k with
    | zero =>
      simp only [List.take_zero, List.drop_zero]
      rfl
    | succ k' =>
      have hKLt : k' < right.length := by omega
      simp only [List.take_succ_cons, List.drop_succ_cons]
      rw [shiftLeftOne_cons_nil]
      -- Rewrite right.take (k'+1) = right.take k' ++ [right[k']] to expose dropLast/getLastD.
      rw [List.take_succ_eq_append_getElem hKLt]
      rw [show c :: (right.take k' ++ [right[k']'hKLt])
           = (c :: right.take k') ++ [right[k']'hKLt] from rfl]
      rw [List.dropLast_concat, List.getLastD_concat]
      rw [(List.drop_eq_getElem_cons hKLt).symm]
  | cons l ls =>
    rw [shiftLeftOne_singleton_cons, encodeConfig_singleton, encodeConfig_singleton]
    rw [decodePadded_proper_form (k + 1) ls (c :: right) l
          (by simp; omega),
        decodePadded_proper_form (k + 1) (l :: ls) right c
          (by simp; omega)]
    simp only [Option.map_some, Nat.add_sub_cancel]
    cases k with
    | zero =>
      simp only [List.take_zero, List.drop_zero]
      rfl
    | succ k' =>
      have hKLt : k' < right.length := by omega
      simp only [List.take_succ_cons, List.drop_succ_cons]
      rw [shiftLeftOne_cons_cons]
      rw [List.take_succ_eq_append_getElem hKLt]
      rw [show c :: (right.take k' ++ [right[k']'hKLt])
           = (c :: right.take k') ++ [right[k']'hKLt] from rfl]
      rw [List.dropLast_concat, List.getLastD_concat]
      rw [(List.drop_eq_getElem_cons hKLt).symm]

/-- Full bridge for shiftRight: by induction on `mag` using `decodePadded_shiftRightOne`.
    Unconditional — works for any [c]-view. -/
private theorem decodePadded_shiftByRight (w : Nat) (hw : w ≥ 1) :
    ∀ (mag : Nat) (left right : List Nat) (c : Nat),
    decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftBy
        { left := left, cells := [c], right := right } mag false)) =
    (decodeConfigPadded w (encodeConfig
        { left := left, cells := [c], right := right })).map
      (fun X => GeneralizedShift.shiftBy X mag false) := by
  intro mag
  induction mag with
  | zero =>
    intro left right c
    simp only [GeneralizedShift.shiftBy]
    cases decodeConfigPadded w (encodeConfig
      { left := left, cells := [c], right := right }) <;> rfl
  | succ n ih =>
    intro left right c
    -- shiftBy X (n+1) false = shiftBy (shiftRightOne X) n false.
    -- Apply per-step bridge: decodePadded ∘ encode ∘ shiftRightOne = .map shiftRightOne ∘ decodePadded ∘ encode.
    -- Then ih on the original X (not shiftRightOne X), composing with shiftRightOne.
    show decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftBy
            (GeneralizedShift.shiftRightOne
              { left := left, cells := [c], right := right }) n false)) = _
    cases right with
    | nil =>
      rw [show GeneralizedShift.shiftRightOne { left := left, cells := [c], right := [] }
            = { left := c :: left, cells := [0], right := [] } from rfl]
      rw [ih (c :: left) [] 0]
      rw [show decodeConfigPadded w (encodeConfig
              { left := c :: left, cells := [0], right := [] })
            = decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftRightOne
                { left := left, cells := [c], right := [] })) from rfl]
      rw [decodePadded_shiftRightOne w hw left [] c]
      rw [Option.map_map]
      rfl
    | cons r rs =>
      rw [show GeneralizedShift.shiftRightOne
              { left := left, cells := [c], right := r :: rs }
            = { left := c :: left, cells := [r], right := rs } from rfl]
      rw [ih (c :: left) rs r]
      rw [show decodeConfigPadded w (encodeConfig
              { left := c :: left, cells := [r], right := rs })
            = decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftRightOne
                { left := left, cells := [c], right := r :: rs })) from rfl]
      rw [decodePadded_shiftRightOne w hw left (r :: rs) c]
      rw [Option.map_map]
      rfl

/-- Full bridge for shiftLeft: by induction on `mag` using `decodePadded_shiftLeftOne`.
    Requires `right.length ≥ w - 1` (preserved by shiftLeft, which only grows right). -/
private theorem decodePadded_shiftByLeft (w : Nat) (hw : w ≥ 1) :
    ∀ (mag : Nat) (left right : List Nat) (c : Nat), right.length ≥ w - 1 →
    decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftBy
        { left := left, cells := [c], right := right } mag true)) =
    (decodeConfigPadded w (encodeConfig
        { left := left, cells := [c], right := right })).map
      (fun X => GeneralizedShift.shiftBy X mag true) := by
  intro mag
  induction mag with
  | zero =>
    intro left right c _
    simp only [GeneralizedShift.shiftBy]
    cases decodeConfigPadded w (encodeConfig
      { left := left, cells := [c], right := right }) <;> rfl
  | succ n ih =>
    intro left right c hRightLen
    show decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftBy
            (GeneralizedShift.shiftLeftOne
              { left := left, cells := [c], right := right }) n true)) = _
    cases left with
    | nil =>
      rw [show GeneralizedShift.shiftLeftOne { left := [], cells := [c], right := right }
            = { left := [], cells := [0], right := c :: right } from rfl]
      rw [ih [] (c :: right) 0 (by simp; omega)]
      rw [show decodeConfigPadded w (encodeConfig
              { left := [], cells := [0], right := c :: right })
            = decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftLeftOne
                { left := [], cells := [c], right := right })) from rfl]
      rw [decodePadded_shiftLeftOne w hw [] right c hRightLen]
      rw [Option.map_map]
      rfl
    | cons l ls =>
      rw [show GeneralizedShift.shiftLeftOne { left := l :: ls, cells := [c], right := right }
            = { left := ls, cells := [l], right := c :: right } from rfl]
      rw [ih ls (c :: right) l (by simp; omega)]
      rw [show decodeConfigPadded w (encodeConfig
              { left := ls, cells := [l], right := c :: right })
            = decodeConfigPadded w (encodeConfig (GeneralizedShift.shiftLeftOne
                { left := l :: ls, cells := [c], right := right })) from rfl]
      rw [decodePadded_shiftLeftOne w hw (l :: ls) right c hRightLen]
      rw [Option.map_map]
      rfl

/-- Helper: getListElem of a cons list at a successor index reduces to the
    list's element at the predecessor index (when in range). -/
private theorem getListElem_cons_succ (a : Nat) (as : List Nat) (n : Nat)
    (h : n < as.length) :
    getListElem (a :: as) (n + 1) = as[n]'h := by
  simp [getListElem, List.getElem?_eq_getElem h]

/-- Helper: replAsc on `a :: as` for k ≤ as.length yields `as.take k`. -/
private theorem replAsc_cons_eq_take (a : Nat) (as : List Nat) :
    ∀ (k : Nat), k ≤ as.length → replAsc (a :: as) k = as.take k := by
  intro k
  induction k with
  | zero => intro _; simp [replAsc]
  | succ n ih =>
    intro hk
    have hn : n ≤ as.length := by omega
    have hLt : n < as.length := by omega
    show replAsc (a :: as) n ++ [getListElem (a :: as) (n + 1)] = as.take (n + 1)
    rw [ih hn, getListElem_cons_succ a as n hLt,
        List.take_succ_eq_append_getElem hLt]

/-- Bridge for the chain output: replAsc repl (w-1) is repl.tail when repl.length = w. -/
private theorem replAsc_eq_tail (repl : List Nat) (w : Nat)
    (hLen : repl.length = w) (hw : w ≥ 1) :
    replAsc repl (w - 1) = repl.tail := by
  cases repl with
  | nil => simp at hLen; omega
  | cons r₀ rs =>
    simp only [List.tail_cons, List.length_cons] at *
    have : w - 1 = rs.length := by omega
    rw [this, replAsc_cons_eq_take r₀ rs rs.length (Nat.le_refl _),
        List.take_length]

-- ============================================================================
-- SimulationEncoding (Moore Theorem 8 in conjugation form)
-- ============================================================================

/-- Moore's Theorem 8 in conjugation form. The decode is `decodeConfigPadded`
    which absorbs the [0]-phantom from short-tape shifts.

    Hypotheses:
    - `hLen`: every reachable GS config has cells of length `windowWidth`.
    - `hShift`: every active window has shift magnitude ≥ 1.
    - `hRepl`: every active window's replacement has length `windowWidth`.
    - `hAlpha`: alphabet size ≥ 1.
    - `hBound`: cells (and replacements of active windows) are bounded by alphabet size.
    - `hHalt`: inactive GS configs encode to halting TM configs. -/
def gsToTMSimulationEncoding (params : GSParams)
    (hAlpha : params.alphabetSize ≥ 1)
    (hWidth : params.windowWidth ≥ 1)
    (hLen : ∀ gsConfig gsConfig',
      GeneralizedShift.step (gsMachine params) gsConfig = some gsConfig' →
      gsConfig.cells.length = params.windowWidth)
    (hShift : ∀ w, params.gsIsActive w = true →
      (params.gsTransition w).shiftMagnitude ≥ 1)
    (hRepl : ∀ w, params.gsIsActive w = true →
      (params.gsTransition w).replacement.length = params.windowWidth)
    (hCellBoundAll : ∀ gsConfig gsConfig',
      GeneralizedShift.step (gsMachine params) gsConfig = some gsConfig' →
      ∀ x, x ∈ gsConfig.cells → x < params.alphabetSize)
    (hHalt : ∀ gsConfig,
      GeneralizedShift.step (gsMachine params) gsConfig = none →
      ComputationalMachine.Halts
        (BiInfiniteTuringMachine.toComputationalMachine (toBiTM params))
        (encodeConfig gsConfig)) :
    ComputationalMachine.SimulationEncoding
      (BiInfiniteTuringMachine.toComputationalMachine (toBiTM params))
      (GeneralizedShift.toComputationalMachine (gsMachine params)) where
  encode := encodeConfig
  decode := decodeConfigPadded params.windowWidth
  commutes := by
    intro b b' h_step
    -- Save useful facts before unfolding.
    have hLenB : b.cells.length = params.windowWidth := hLen b b' h_step
    have hCellBoundB : ∀ x, x ∈ b.cells → x < params.alphabetSize :=
      hCellBoundAll b b' h_step
    -- Now extract the step structure.
    change GeneralizedShift.step (gsMachine params) b = some b' at h_step
    -- Determine activity.
    have hAct : params.gsIsActive b.cells = true := by
      cases hX : params.gsIsActive b.cells with
      | true => rfl
      | false =>
        exfalso
        unfold GeneralizedShift.step gsMachine at h_step
        simp only [hX, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h_step
        cases h_step
    have hReplLen' : (params.gsTransition b.cells).replacement.length = params.windowWidth :=
      hRepl b.cells hAct
    have hMagB : (params.gsTransition b.cells).shiftMagnitude ≥ 1 := hShift b.cells hAct
    -- Compute b' from h_step.
    have hb'Eq : b' = GeneralizedShift.shiftBy
        { b with cells := (params.gsTransition b.cells).replacement }
        (params.gsTransition b.cells).shiftMagnitude
        (params.gsTransition b.cells).shiftLeft := by
      unfold GeneralizedShift.step gsMachine at h_step
      simp only [hAct, not_true_eq_false, ↓reduceIte] at h_step
      exact (Option.some.inj h_step).symm
    -- Decompose b for cleanliness.
    obtain ⟨b_left, b_cells, b_right⟩ := b
    simp only at hLenB hAct hReplLen' hMagB hCellBoundB hb'Eq
    -- Branch on w = 1 vs w ≥ 2.
    by_cases hw1 : params.windowWidth = 1
    case pos =>
      -- w = 1: cells must be [c]. Replacement must be [r]. Use fullSim_w1.
      rw [hw1] at hLenB hReplLen'
      cases b_cells with
      | nil => simp at hLenB
      | cons c rest =>
        cases rest with
        | cons _ _ => simp at hLenB
        | nil =>
          -- b_cells = [c]
          cases hrep : (params.gsTransition [c]).replacement with
          | nil => rw [hrep] at hReplLen'; simp at hReplLen'
          | cons r rest =>
            cases rest with
            | cons _ _ => rw [hrep] at hReplLen'; simp at hReplLen'
            | nil =>
              -- replacement = [r]
              refine ⟨(params.gsTransition [c]).shiftMagnitude,
                      encodeConfig (GeneralizedShift.shiftBy
                        { left := b_left, cells := [r], right := b_right }
                        (params.gsTransition [c]).shiftMagnitude
                        (params.gsTransition [c]).shiftLeft), ?_, ?_⟩
              · rw [BiInfiniteTuringMachine.iterationStep_eq_exactSteps]
                simp only [encodeConfig]
                exact fullSim_w1 params c r hw1 hAct hrep hMagB b_left b_right
              · -- Bridge.
                rw [hb'Eq, hrep]
                -- b' = shiftBy {b_left, [r], b_right} mag dir.
                -- For w = 1, the bridge applies; decodePadded_proper_form simplifies.
                cases hDir : (params.gsTransition [c]).shiftLeft
                · -- shiftRight
                  rw [hw1]
                  rw [decodePadded_shiftByRight 1 (by omega)
                        (params.gsTransition [c]).shiftMagnitude b_left b_right r]
                  rw [encodeConfig_singleton]
                  rw [decodePadded_proper_form 1 b_left b_right r (by omega)]
                  rfl
                · -- shiftLeft
                  rw [hw1]
                  rw [decodePadded_shiftByLeft 1 (by omega)
                        (params.gsTransition [c]).shiftMagnitude b_left b_right r
                        (by omega)]
                  rw [encodeConfig_singleton]
                  rw [decodePadded_proper_form 1 b_left b_right r (by omega)]
                  rfl
    case neg =>
      -- w ≥ 2.
      have hWidth2 : params.windowWidth ≥ 2 := by omega
      refine ⟨2 * (params.windowWidth - 1) +
              (params.gsTransition b_cells).shiftMagnitude,
              encodeConfig (GeneralizedShift.shiftBy
                { left := b_left,
                  cells := [getListElem (params.gsTransition b_cells).replacement 0],
                  right := replAsc (params.gsTransition b_cells).replacement
                    (params.windowWidth - 1) ++ b_right }
                (params.gsTransition b_cells).shiftMagnitude
                (params.gsTransition b_cells).shiftLeft), ?_, ?_⟩
      · rw [BiInfiniteTuringMachine.iterationStep_eq_exactSteps]
        exact fullSim_general_cView params hAlpha hWidth2 b_cells
          (params.gsTransition b_cells).replacement
          hLenB hAct hCellBoundB rfl hReplLen' hMagB b_left b_right
      · -- Bridge.
        rw [hb'Eq]
        have hReplAscLen : (replAsc (params.gsTransition b_cells).replacement
            (params.windowWidth - 1)).length = params.windowWidth - 1 := by
          rw [replAsc_eq_tail _ params.windowWidth hReplLen' (by omega)]
          rw [List.length_tail, hReplLen']
        have hRightLenView : (replAsc (params.gsTransition b_cells).replacement
            (params.windowWidth - 1) ++ b_right).length ≥ params.windowWidth - 1 := by
          rw [List.length_append, hReplAscLen]; omega
        have hReplDecomp : getListElem (params.gsTransition b_cells).replacement 0 ::
            (params.gsTransition b_cells).replacement.tail =
            (params.gsTransition b_cells).replacement := by
          cases hr : (params.gsTransition b_cells).replacement with
          | nil => rw [hr] at hReplLen'; simp at hReplLen'; omega
          | cons r₀ rs =>
            simp only [List.tail_cons]
            show getListElem (r₀ :: rs) 0 :: rs = r₀ :: rs
            simp [getListElem]
        cases hDir : (params.gsTransition b_cells).shiftLeft
        · -- shiftRight
          rw [decodePadded_shiftByRight params.windowWidth hWidth
                (params.gsTransition b_cells).shiftMagnitude b_left
                (replAsc (params.gsTransition b_cells).replacement
                  (params.windowWidth - 1) ++ b_right)
                (getListElem (params.gsTransition b_cells).replacement 0)]
          rw [encodeConfig_singleton]
          rw [decodePadded_proper_form params.windowWidth b_left _ _ hRightLenView]
          simp only [Option.map_some]
          rw [List.take_left' hReplAscLen, List.drop_left' hReplAscLen]
          rw [replAsc_eq_tail _ params.windowWidth hReplLen' (by omega)]
          rw [hReplDecomp]
          rfl
        · -- shiftLeft
          rw [decodePadded_shiftByLeft params.windowWidth hWidth
                (params.gsTransition b_cells).shiftMagnitude b_left
                (replAsc (params.gsTransition b_cells).replacement
                  (params.windowWidth - 1) ++ b_right)
                (getListElem (params.gsTransition b_cells).replacement 0)
                hRightLenView]
          rw [encodeConfig_singleton]
          rw [decodePadded_proper_form params.windowWidth b_left _ _ hRightLenView]
          simp only [Option.map_some]
          rw [List.take_left' hReplAscLen, List.drop_left' hReplAscLen]
          rw [replAsc_eq_tail _ params.windowWidth hReplLen' (by omega)]
          rw [hReplDecomp]
          rfl
  halting := by
    intro b h_step; exact hHalt b h_step

end GeneralizedShiftToTuringMachine
