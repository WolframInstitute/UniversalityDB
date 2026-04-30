/-
  TMtoGS

  TM → GS simulation (Moore Theorem 7), conjugation form.

  Setup:
  - encode = `encodeBiTM` (Moore's exact)
  - decode = `decodeBiTMNormalized` (decodes back, post-strips trailing zeros)
  - B side = `BiInfiniteTuringMachine.toComputationalMachineNormalized`,
    whose step is Moore's step post-composed with `stripConfig`.

  With this choice, `commutes` reads as the strict conjugation
  `step_B(b) = decode (step_A^n (encode b))` — no `modulo normalize` qualifier.
  The bridge between Moore's exact step and the normalized step is
  `BiInfiniteTuringMachine.step_stripConfig_bisim` (a separate lemma).

  Contents:
  - `biTMStepUniform`: a `headD`/`tail` reformulation of `BiInfiniteTuringMachine.step`
    that sidesteps case-split explosion in tactic proofs.
  - `normalize_consHeadD_dropOne` — the algebraic heart of the proof.
  - `normalizeBiTMConfig`/`decodeBiTMNormalized` (BiTM-side decoder helpers).
  - `normalizeBiTMConfig_eq_stripConfig` — bridge to the BiTM canonical form.
  - `tmToGSCommutesMoore` — the existing core proof against Moore's exact step.
  - The main theorem `tmToGSSimulation` — thin wrapper for the conjugation form.
-/

import Machines.BiInfiniteTuringMachine.Defs
import Machines.GeneralizedShift.Defs
import Proofs.TuringMachineToGeneralizedShift
import SimulationEncoding

namespace TMtoGS

/- ============================================================================
   Uniform reformulation of `BiInfiniteTuringMachine.step` (using `headD`/`tail`
   instead of `match config.left/right with []|x::xs`). Avoids case-split
   explosion in tactic proofs; has a one-line equivalence proof.
   ============================================================================ -/
def biTMStepUniform (machine : TuringMachine.Machine)
    (config : BiInfiniteTuringMachine.Configuration) :
    Option BiInfiniteTuringMachine.Configuration :=
  if config.state = 0 then none
  else
    let rule := machine.transition config.state config.head
    match rule.direction with
    | TuringMachine.Direction.L =>
      some { state := rule.nextState
             left  := config.left.tail
             head  := config.left.headD 0
             right := rule.write :: config.right }
    | TuringMachine.Direction.R =>
      some { state := rule.nextState
             left  := rule.write :: config.left
             head  := config.right.headD 0
             right := config.right.tail }

theorem biTMStep_eq_uniform (machine : TuringMachine.Machine)
    (config : BiInfiniteTuringMachine.Configuration) :
    BiInfiniteTuringMachine.step machine config = biTMStepUniform machine config := by
  unfold BiInfiniteTuringMachine.step biTMStepUniform BiInfiniteTuringMachine.readHead
  by_cases h : config.state = 0
  · simp [h]
  · simp [h, show (config.state == 0) = false from by simp [h]]
    cases (machine.transition config.state config.head).direction
    · cases config.left <;> rfl
    · cases config.right <;> rfl

/- ============================================================================
   The algebraic heart: the `headD :: dropOne` reconstruction strips back to
   the original. This handles the `[0]` phantom: when `xs = []`, the LHS is
   `normalize [0] = []`, equal to `normalize [] = []`.
   ============================================================================ -/

theorem normalize_consHeadD_dropOne (xs : List Nat) :
    TuringMachineToGeneralizedShift.normalize ((xs.headD 0) :: xs.drop 1) =
      TuringMachineToGeneralizedShift.normalize xs := by
  cases xs with
  | nil =>
    show TuringMachineToGeneralizedShift.normalize [0] = TuringMachineToGeneralizedShift.normalize []
    simp [TuringMachineToGeneralizedShift.normalize]
  | cons x xs' => simp [List.headD, List.drop]

/- ============================================================================
   BiTM-side normalization helpers
   ============================================================================ -/

/-- Canonicalize a BiTM configuration by stripping trailing zeros from its tapes. -/
def normalizeBiTMConfig (c : BiInfiniteTuringMachine.Configuration) :
    BiInfiniteTuringMachine.Configuration :=
  { state := c.state
    left  := TuringMachineToGeneralizedShift.normalize c.left
    head  := c.head
    right := TuringMachineToGeneralizedShift.normalize c.right }

/-- Decode + canonicalize: decode the GS config back to BiTM, then strip
    trailing zeros from its tapes. Absorbs the `[0]` phantom. -/
def decodeBiTMNormalized (machine : TuringMachine.Machine)
    (gsConfig : GeneralizedShift.Configuration) :
    Option BiInfiniteTuringMachine.Configuration :=
  (TuringMachineToGeneralizedShift.decodeBiTM machine gsConfig).map normalizeBiTMConfig

/-- `TuringMachineToGeneralizedShift.normalize` and
    `BiInfiniteTuringMachine.stripTrailingZeros` are the same function
    (literally identical bodies in different namespaces). -/
theorem normalize_eq_stripTrailingZeros (xs : List Nat) :
    TuringMachineToGeneralizedShift.normalize xs =
      BiInfiniteTuringMachine.stripTrailingZeros xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show (if (TuringMachineToGeneralizedShift.normalize xs).isEmpty && x == 0
          then [] else x :: TuringMachineToGeneralizedShift.normalize xs) =
         (if (BiInfiniteTuringMachine.stripTrailingZeros xs).isEmpty && x == 0
          then [] else x :: BiInfiniteTuringMachine.stripTrailingZeros xs)
    rw [ih]

/-- Configuration-level: `normalizeBiTMConfig = stripConfig`. -/
theorem normalizeBiTMConfig_eq_stripConfig (c : BiInfiniteTuringMachine.Configuration) :
    normalizeBiTMConfig c = BiInfiniteTuringMachine.stripConfig c := by
  unfold normalizeBiTMConfig BiInfiniteTuringMachine.stripConfig
  rw [normalize_eq_stripTrailingZeros, normalize_eq_stripTrailingZeros]

/-- Helper: decoding-then-normalizing the encoding of any well-formed BiTM
    config recovers the canonical (normalized) form of that config. -/
theorem decodeBiTMNormalized_encode_eq (machine : TuringMachine.Machine)
    (hk : machine.numberOfSymbols > 0)
    (b : BiInfiniteTuringMachine.Configuration)
    (hh : b.head < machine.numberOfSymbols) :
    decodeBiTMNormalized machine (TuringMachineToGeneralizedShift.encodeBiTM machine b) =
    some (normalizeBiTMConfig b) := by
  unfold decodeBiTMNormalized TuringMachineToGeneralizedShift.decodeBiTM
    TuringMachineToGeneralizedShift.encodeBiTM
  by_cases hs : b.state = 0
  · -- halted: cells[1] = b.head < k → if-pos branch
    simp only [hs, ↓reduceIte, if_pos hh, Option.map_some]
    unfold normalizeBiTMConfig
    congr 1
    rw [BiInfiniteTuringMachine.Configuration.mk.injEq]
    refine ⟨hs.symm, ?_, rfl, ?_⟩
    · cases b.left with
      | nil => rfl
      | cons lh lt => rfl
    · cases b.right with
      | nil => rfl
      | cons rh rt => rfl
  · -- active: cells[1] = encodeActive ... ≥ k → if-neg branch + decodeActiveEncodeActive
    have hState : b.state ≥ 1 := Nat.pos_of_ne_zero hs
    have hDecodeAct := TuringMachineToGeneralizedShift.decodeActiveEncodeActive
      machine.numberOfSymbols b.state b.head hState hh hk
    have hA_ge : ¬ (TuringMachineToGeneralizedShift.encodeActive
        machine.numberOfSymbols b.state b.head < machine.numberOfSymbols) := by
      unfold TuringMachineToGeneralizedShift.encodeActive
      omega
    simp only [hs, ↓reduceIte, if_neg hA_ge, hDecodeAct, Option.map_some]
    unfold normalizeBiTMConfig
    congr 1
    rw [BiInfiniteTuringMachine.Configuration.mk.injEq]
    refine ⟨rfl, ?_, rfl, ?_⟩
    · cases b.left with
      | nil => rfl
      | cons lh lt => rfl
    · cases b.right with
      | nil => rfl
      | cons rh rt => rfl

/- ============================================================================
   Core commutes against Moore's exact step.

   Given `step machine b = some moore_b'`, produces an n-step GS witness `a`
   with `decode a = some (normalizeBiTMConfig moore_b')`. The thin wrapper
   `tmToGSSimulation` then bridges this to the normalized-step conjugation
   `decode a = some b'` where `b' = stripConfig moore_b'`.
   ============================================================================ -/

theorem tmToGSCommutesMoore (machine : TuringMachine.Machine)
    (hk : machine.numberOfSymbols > 0)
    (hHeadAll : ∀ c : BiInfiniteTuringMachine.Configuration,
      c.head < machine.numberOfSymbols)
    (b moore_b' : BiInfiniteTuringMachine.Configuration)
    (h_step : BiInfiniteTuringMachine.step machine b = some moore_b') :
    ∃ n a, (GeneralizedShift.toComputationalMachine
              (TuringMachineToGeneralizedShift.fromBiTM machine)).iterationStep n
              (TuringMachineToGeneralizedShift.encodeBiTM machine b) = some a ∧
           decodeBiTMNormalized machine a = some (normalizeBiTMConfig moore_b') := by
  have hState : b.state ≥ 1 := by
    cases hs : b.state with
    | zero => simp [BiInfiniteTuringMachine.step, hs] at h_step
    | succ n => omega
  have hne : b.state ≠ 0 := by omega
  have hc : b.head < machine.numberOfSymbols := hHeadAll b
  rw [biTMStep_eq_uniform] at h_step
  unfold biTMStepUniform at h_step
  simp only [hne, ↓reduceIte] at h_step
  cases hdir : (machine.transition b.state b.head).direction with
  | L =>
    rw [hdir] at h_step
    injection h_step with hb'
    subst hb'
    have hLeftHead : b.left.headD 0 < machine.numberOfSymbols :=
      hHeadAll { state := (machine.transition b.state b.head).nextState
                 left := b.left.tail
                 head := b.left.headD 0
                 right := (machine.transition b.state b.head).write :: b.right }
    by_cases hns : (machine.transition b.state b.head).nextState = 0
    · refine ⟨1,
        { left := (b.left.drop 1).tail
          cells := [(b.left.drop 1).headD 0
                    , b.left.headD 0
                    , (machine.transition b.state b.head).write]
          right := b.right.headD 0 :: b.right.drop 1 }, ?_, ?_⟩
      · have hDecodeAct := TuringMachineToGeneralizedShift.decodeActiveEncodeActive
          machine.numberOfSymbols b.state b.head hState hc hk
        have hA_ge : ¬ (TuringMachineToGeneralizedShift.encodeActive
            machine.numberOfSymbols b.state b.head < machine.numberOfSymbols) := by
          unfold TuringMachineToGeneralizedShift.encodeActive
          omega
        rw [GeneralizedShift.iterationStep_eq_exactSteps]
        unfold GeneralizedShift.exactSteps
        cases h_gs : GeneralizedShift.step
                       (TuringMachineToGeneralizedShift.fromBiTM machine)
                       (TuringMachineToGeneralizedShift.encodeBiTM machine b) with
        | none =>
          exfalso
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM at h_gs
          simp [hne, hA_ge] at h_gs
        | some a =>
          show some a = _
          rw [← h_gs]
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM
          simp [hne, hDecodeAct, hdir, hns, if_neg hA_ge,
                GeneralizedShift.shiftBy, GeneralizedShift.shiftLeftOne]
          cases b.left with
          | nil => cases b.right <;> rfl
          | cons lh lt => cases lt <;> cases b.right <;> rfl
      · unfold decodeBiTMNormalized TuringMachineToGeneralizedShift.decodeBiTM
          normalizeBiTMConfig
        simp only [if_pos hLeftHead, Option.map_some]
        congr 1
        rw [BiInfiniteTuringMachine.Configuration.mk.injEq]
        refine ⟨hns.symm, ?_, rfl, ?_⟩
        · cases b.left with
          | nil => rfl
          | cons lh lt =>
            show TuringMachineToGeneralizedShift.normalize (lt.headD 0 :: lt.tail) = _
            have h := normalize_consHeadD_dropOne lt
            show TuringMachineToGeneralizedShift.normalize (lt.headD 0 :: lt.tail) =
                  TuringMachineToGeneralizedShift.normalize lt
            cases lt with
            | nil => rfl
            | cons _ _ => exact h
        · apply TuringMachineToGeneralizedShift.normalize_cons_congr
          exact normalize_consHeadD_dropOne b.right
    · have hns_pos : (machine.transition b.state b.head).nextState ≥ 1 :=
        Nat.pos_of_ne_zero hns
      refine ⟨1,
        { left := (b.left.drop 1).tail
          cells := [(b.left.drop 1).headD 0
                    , TuringMachineToGeneralizedShift.encodeActive machine.numberOfSymbols
                        (machine.transition b.state b.head).nextState (b.left.headD 0)
                    , (machine.transition b.state b.head).write]
          right := b.right.headD 0 :: b.right.drop 1 }, ?_, ?_⟩
      · have hDecodeAct := TuringMachineToGeneralizedShift.decodeActiveEncodeActive
          machine.numberOfSymbols b.state b.head hState hc hk
        have hA_ge : ¬ (TuringMachineToGeneralizedShift.encodeActive
            machine.numberOfSymbols b.state b.head < machine.numberOfSymbols) := by
          unfold TuringMachineToGeneralizedShift.encodeActive
          omega
        rw [GeneralizedShift.iterationStep_eq_exactSteps]
        unfold GeneralizedShift.exactSteps
        cases h_gs : GeneralizedShift.step
                       (TuringMachineToGeneralizedShift.fromBiTM machine)
                       (TuringMachineToGeneralizedShift.encodeBiTM machine b) with
        | none =>
          exfalso
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM at h_gs
          simp [hne, hA_ge] at h_gs
        | some a =>
          show some a = _
          rw [← h_gs]
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM
          simp [hne, hDecodeAct, hdir, hns, if_neg hA_ge,
                GeneralizedShift.shiftBy, GeneralizedShift.shiftLeftOne]
          cases b.left with
          | nil => cases b.right <;> rfl
          | cons lh lt => cases lt <;> cases b.right <;> rfl
      · have hDecodeAct2 := TuringMachineToGeneralizedShift.decodeActiveEncodeActive
          machine.numberOfSymbols (machine.transition b.state b.head).nextState
          (b.left.headD 0) hns_pos hLeftHead hk
        have hA_ge2 : ¬ (TuringMachineToGeneralizedShift.encodeActive
            machine.numberOfSymbols (machine.transition b.state b.head).nextState
            (b.left.headD 0) < machine.numberOfSymbols) := by
          unfold TuringMachineToGeneralizedShift.encodeActive
          omega
        unfold decodeBiTMNormalized TuringMachineToGeneralizedShift.decodeBiTM
          normalizeBiTMConfig
        simp only [if_neg hA_ge2, hDecodeAct2, Option.map_some]
        congr 1
        rw [BiInfiniteTuringMachine.Configuration.mk.injEq]
        refine ⟨rfl, ?_, rfl, ?_⟩
        · cases b.left with
          | nil => rfl
          | cons lh lt =>
            show TuringMachineToGeneralizedShift.normalize (lt.headD 0 :: lt.tail) = _
            have h := normalize_consHeadD_dropOne lt
            show TuringMachineToGeneralizedShift.normalize (lt.headD 0 :: lt.tail) =
                  TuringMachineToGeneralizedShift.normalize lt
            cases lt with
            | nil => rfl
            | cons _ _ => exact h
        · apply TuringMachineToGeneralizedShift.normalize_cons_congr
          exact normalize_consHeadD_dropOne b.right
  | R =>
    rw [hdir] at h_step
    injection h_step with hb'
    subst hb'
    by_cases hns : (machine.transition b.state b.head).nextState = 0
    · have hRightHead : b.right.headD 0 < machine.numberOfSymbols :=
        hHeadAll { state := (machine.transition b.state b.head).nextState
                   left := (machine.transition b.state b.head).write :: b.left
                   head := b.right.headD 0
                   right := b.right.tail }
      refine ⟨1,
        { left := b.left.headD 0 :: b.left.drop 1
          cells := [(machine.transition b.state b.head).write
                    , b.right.headD 0
                    , (b.right.drop 1).headD 0]
          right := (b.right.drop 1).tail }, ?_, ?_⟩
      · have hDecodeAct := TuringMachineToGeneralizedShift.decodeActiveEncodeActive
          machine.numberOfSymbols b.state b.head hState hc hk
        have hA_ge : ¬ (TuringMachineToGeneralizedShift.encodeActive
            machine.numberOfSymbols b.state b.head < machine.numberOfSymbols) := by
          unfold TuringMachineToGeneralizedShift.encodeActive
          omega
        rw [GeneralizedShift.iterationStep_eq_exactSteps]
        unfold GeneralizedShift.exactSteps
        cases h_gs : GeneralizedShift.step
                       (TuringMachineToGeneralizedShift.fromBiTM machine)
                       (TuringMachineToGeneralizedShift.encodeBiTM machine b) with
        | none =>
          exfalso
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM at h_gs
          simp [hne, hA_ge] at h_gs
        | some a =>
          show some a = _
          rw [← h_gs]
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM
          simp [hne, hDecodeAct, hdir, hns, if_neg hA_ge,
                GeneralizedShift.shiftBy, GeneralizedShift.shiftRightOne]
          cases b.right with
          | nil => cases b.left <;> rfl
          | cons rh rt => cases rt <;> cases b.left <;> rfl
      · unfold decodeBiTMNormalized TuringMachineToGeneralizedShift.decodeBiTM
          normalizeBiTMConfig
        simp only [if_pos hRightHead, Option.map_some]
        congr 1
        rw [BiInfiniteTuringMachine.Configuration.mk.injEq]
        refine ⟨hns.symm, ?_, rfl, ?_⟩
        · apply TuringMachineToGeneralizedShift.normalize_cons_congr
          exact normalize_consHeadD_dropOne b.left
        · cases b.right with
          | nil => rfl
          | cons rh rt =>
            show TuringMachineToGeneralizedShift.normalize (rt.headD 0 :: rt.tail) = _
            have h := normalize_consHeadD_dropOne rt
            show TuringMachineToGeneralizedShift.normalize (rt.headD 0 :: rt.tail) =
                  TuringMachineToGeneralizedShift.normalize rt
            cases rt with
            | nil => rfl
            | cons _ _ => exact h
    · refine ⟨1,
        { left := b.left.headD 0 :: b.left.drop 1
          cells := [(machine.transition b.state b.head).write
                    , TuringMachineToGeneralizedShift.encodeActive machine.numberOfSymbols
                        (machine.transition b.state b.head).nextState (b.right.headD 0)
                    , (b.right.drop 1).headD 0]
          right := (b.right.drop 1).tail }, ?_, ?_⟩
      · have hDecodeAct := TuringMachineToGeneralizedShift.decodeActiveEncodeActive
          machine.numberOfSymbols b.state b.head hState hc hk
        have hA_ge : ¬ (TuringMachineToGeneralizedShift.encodeActive
            machine.numberOfSymbols b.state b.head < machine.numberOfSymbols) := by
          unfold TuringMachineToGeneralizedShift.encodeActive
          omega
        rw [GeneralizedShift.iterationStep_eq_exactSteps]
        unfold GeneralizedShift.exactSteps
        cases h_gs : GeneralizedShift.step
                       (TuringMachineToGeneralizedShift.fromBiTM machine)
                       (TuringMachineToGeneralizedShift.encodeBiTM machine b) with
        | none =>
          exfalso
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM at h_gs
          simp [hne, hA_ge] at h_gs
        | some a =>
          show some a = _
          rw [← h_gs]
          unfold GeneralizedShift.step TuringMachineToGeneralizedShift.encodeBiTM
            TuringMachineToGeneralizedShift.fromBiTM
          simp [hne, hDecodeAct, hdir, hns, if_neg hA_ge,
                GeneralizedShift.shiftBy, GeneralizedShift.shiftRightOne]
          cases b.right with
          | nil => cases b.left <;> rfl
          | cons rh rt => cases rt <;> cases b.left <;> rfl
      · have hns_pos : (machine.transition b.state b.head).nextState ≥ 1 :=
          Nat.pos_of_ne_zero hns
        have hRightHead : b.right.headD 0 < machine.numberOfSymbols :=
          hHeadAll { state := (machine.transition b.state b.head).nextState
                     left := (machine.transition b.state b.head).write :: b.left
                     head := b.right.headD 0
                     right := b.right.tail }
        have hDecodeAct2 := TuringMachineToGeneralizedShift.decodeActiveEncodeActive
          machine.numberOfSymbols (machine.transition b.state b.head).nextState
          (b.right.headD 0) hns_pos hRightHead hk
        have hA_ge2 : ¬ (TuringMachineToGeneralizedShift.encodeActive
            machine.numberOfSymbols (machine.transition b.state b.head).nextState
            (b.right.headD 0) < machine.numberOfSymbols) := by
          unfold TuringMachineToGeneralizedShift.encodeActive
          omega
        unfold decodeBiTMNormalized TuringMachineToGeneralizedShift.decodeBiTM
          normalizeBiTMConfig
        simp only [if_neg hA_ge2, hDecodeAct2, Option.map_some]
        congr 1
        rw [BiInfiniteTuringMachine.Configuration.mk.injEq]
        refine ⟨rfl, ?_, rfl, ?_⟩
        · apply TuringMachineToGeneralizedShift.normalize_cons_congr
          exact normalize_consHeadD_dropOne b.left
        · cases b.right with
          | nil => rfl
          | cons rh rt =>
            show TuringMachineToGeneralizedShift.normalize (rt.headD 0 :: rt.tail) = _
            have h := normalize_consHeadD_dropOne rt
            show TuringMachineToGeneralizedShift.normalize (rt.headD 0 :: rt.tail) =
                  TuringMachineToGeneralizedShift.normalize rt
            cases rt with
            | nil => rfl
            | cons _ _ => exact h

/- ============================================================================
   The main theorem: TM → GS simulation in conjugation form against the
   normalized BiTM step. Closed (no `sorry`).
   ============================================================================ -/

/-- **TM → GS edge** (Moore Theorem 7): every BiTM step (post-stripped to
    canonical form) lifts to one standard-GS step, and decoding the result
    recovers `b'` exactly — no `modulo normalize` qualifier.

    Closed proof; conditional only on machine well-formedness. -/
def tmToGSSimulation (machine : TuringMachine.Machine)
    (_hk : machine.numberOfSymbols > 0)
    (_hHeadAll : ∀ c : BiInfiniteTuringMachine.Configuration,
      c.head < machine.numberOfSymbols)
    (_hWriteBound : ∀ q a, (machine.transition q a).write < machine.numberOfSymbols)
    (_hStateBound : ∀ q a, (machine.transition q a).nextState ≤ machine.numberOfStates) :
    ComputationalMachine.SimulationEncoding
      (GeneralizedShift.toComputationalMachine
        (TuringMachineToGeneralizedShift.fromBiTM machine))
      (BiInfiniteTuringMachine.toComputationalMachineNormalized machine) where
  encode := TuringMachineToGeneralizedShift.encodeBiTM machine
  decode := decodeBiTMNormalized machine
  commutes := by
    intro b b' h_step
    -- Unpack stepNormalized = some b' as ∃ moore_b', step = some moore_b' ∧ b' = stripConfig moore_b'.
    change BiInfiniteTuringMachine.stepNormalized machine b = some b' at h_step
    unfold BiInfiniteTuringMachine.stepNormalized at h_step
    cases h_moore : BiInfiniteTuringMachine.step machine b with
    | none => rw [h_moore] at h_step; simp at h_step
    | some moore_b' =>
      rw [h_moore, Option.map_some] at h_step
      injection h_step with h_b_eq
      -- h_b_eq : stripConfig moore_b' = b'
      obtain ⟨n, a, ha_step, ha_decode⟩ :=
        tmToGSCommutesMoore machine _hk _hHeadAll b moore_b' h_moore
      refine ⟨n, a, ha_step, ?_⟩
      rw [ha_decode, normalizeBiTMConfig_eq_stripConfig, h_b_eq]
      rfl
  halting := by
    intro config h_step
    -- Unpack stepNormalized = none as step = none.
    change BiInfiniteTuringMachine.stepNormalized machine config = none at h_step
    unfold BiInfiniteTuringMachine.stepNormalized at h_step
    have h_moore : BiInfiniteTuringMachine.step machine config = none := by
      cases h : BiInfiniteTuringMachine.step machine config with
      | none => rfl
      | some _ => rw [h] at h_step; simp at h_step
    -- Now the original halting argument applies.
    have hState : config.state = 0 := by
      cases hs : config.state with
      | zero => rfl
      | succ n =>
        exfalso
        unfold BiInfiniteTuringMachine.step at h_moore
        split at h_moore
        · next hbeq => exact absurd (eq_of_beq hbeq) (by omega)
        · dsimp at h_moore; split at h_moore <;> simp at h_moore
    have hlt : config.head < machine.numberOfSymbols := _hHeadAll config
    refine ⟨1, ?_⟩
    show GeneralizedShift.step (TuringMachineToGeneralizedShift.fromBiTM machine)
          (TuringMachineToGeneralizedShift.encodeBiTM machine config) >>= _ = none
    have : GeneralizedShift.step (TuringMachineToGeneralizedShift.fromBiTM machine)
            (TuringMachineToGeneralizedShift.encodeBiTM machine config) = none := by
      simp [TuringMachineToGeneralizedShift.encodeBiTM
          , TuringMachineToGeneralizedShift.fromBiTM
          , GeneralizedShift.step, hState
          , show ¬ (config.head ≥ machine.numberOfSymbols) from by omega]
    rw [this]; rfl

end TMtoGS
