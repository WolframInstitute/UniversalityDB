/-
  TagSystem.TagToCyclicTagSystem

  Cook's encoding: 2-Tag System -> Cyclic Tag System.

  Each symbol ai of the k-symbol tag alphabet is encoded as a binary
  word of length k: one-hot encoding with true at position i.
  A tag word is encoded by concatenating the binary encodings.
  The CTS has k appendants, where appendant j = encoding(production(aj)).

  One step of the 2-tag system corresponds to 2k steps of the CTS.
-/

import Machines.TagSystem.Defs
import SimulationEncoding

namespace TagSystem

-- ============================================================================
-- Symbol encoding: Fin k -> List Bool
-- ============================================================================

/-- Encode a tag alphabet symbol as a one-hot binary word of length k.
    Symbol i becomes: [false, ..., false, true, false, ..., false]
    with `true` at position i (0-indexed). -/
def symbolEncode (k : Nat) (i : Fin k) : List Bool :=
  (List.range k).map fun j => j == i.val

/-- symbolEncode always produces a list of length k -/
theorem symbolEncodeLength (k : Nat) (i : Fin k) :
    (symbolEncode k i).length = k := by
  simp [symbolEncode]

-- ============================================================================
-- Word encoding: List (Fin k) -> List Bool
-- ============================================================================

/-- Encode a tag system word as a binary string by concatenating
    the one-hot encodings of each symbol. -/
def tagWordEncode (k : Nat) (word : List (Fin k)) : List Bool :=
  word.flatMap (symbolEncode k)

/-- The encoded word length is k times the original word length -/
theorem tagWordEncodeLength (k : Nat) (word : List (Fin k)) :
    (tagWordEncode k word).length = k * word.length := by
  induction word with
  | nil => simp [tagWordEncode]
  | cons a rest ih =>
    simp only [tagWordEncode, List.flatMap_cons, List.length_append, symbolEncodeLength]
    change k + (tagWordEncode k rest).length = k * (rest.length + 1)
    rw [ih, Nat.mul_succ]; exact Nat.add_comm _ _

/-- Empty tag word encodes to empty CTS data -/
theorem tagWordEncodeNil (k : Nat) : tagWordEncode k ([] : List (Fin k)) = [] := by
  simp [tagWordEncode]

/-- tagWordEncode distributes over list append -/
theorem tagWordEncodeAppend (k : Nat) (xs ys : List (Fin k)) :
    tagWordEncode k (xs ++ ys) = tagWordEncode k xs ++ tagWordEncode k ys := by
  simp [tagWordEncode, List.flatMap_append]

/-- tagWordEncode of a cons = symbolEncode of head ++ tagWordEncode of tail -/
theorem tagWordEncodeCons (k : Nat) (a : Fin k) (rest : List (Fin k)) :
    tagWordEncode k (a :: rest) = symbolEncode k a ++ tagWordEncode k rest := by
  simp [tagWordEncode, List.flatMap_cons]

-- ============================================================================
-- CTS construction from a 2-Tag System
-- ============================================================================

/-- Construct a Cyclic Tag System that simulates a given 2-tag system.

    Cook's encoding uses **2k appendants** (not k):
    - Appendants 0..k-1:   encode production(aj) as tagWordEncode k (productions(aj))
    - Appendants k..2k-1:  all empty (consume the second deleted symbol silently)

    One 2-tag step on word `a :: b :: rest -> rest ++ productions(a)` corresponds
    to 2k CTS steps:
    - First k steps process `symbolEncode k a`: the one-hot bit at position a.val
      fires appendant[a.val] = tagWordEncode(productions(a)), appending the correct production
    - Next k steps process `symbolEncode k b`: the one-hot bit at position b.val
      fires appendant[k + b.val] = [] (empty), so nothing is appended

    Reference: Cook, "Universality in Elementary Cellular Automata" (2004). -/
def tagToCyclicTagSystem {k : Nat} (ts : Tag k) (hk : k > 0) : CyclicTagSystem where
  appendants :=
    -- First k: production encodings
    (List.finRange k).map (fun i => tagWordEncode k (ts.productions i))
    -- Next k: empty (for consuming the second deleted symbol)
    ++ (List.finRange k).map (fun _ => ([] : List Bool))
  nonempty := by simp; omega

/-- The constructed CTS has exactly 2*k appendants -/
theorem tagToCyclicTagSystemAppendantsLength {k : Nat} (ts : Tag k) (hk : k > 0) :
    (tagToCyclicTagSystem ts hk).appendants.length = 2 * k := by
  simp [tagToCyclicTagSystem]; omega

-- ============================================================================
-- Encoding a TagConfiguration into a CyclicTagSystemConfiguration
-- ============================================================================

/-- Encode a tag system configuration into a CTS configuration. -/
def tagConfigurationToCyclicTagSystem (k : Nat) (cfg : TagConfiguration k) : CyclicTagSystemConfiguration where
  data := tagWordEncode k cfg
  phase := 0

-- ============================================================================
-- CTS structural lemmas
-- ============================================================================

/-- CTS halts immediately on empty data -/
theorem cyclicTagSystemHaltsOnEmpty (cts : CyclicTagSystem) (phase : Nat) :
    cts.Halts { data := [], phase := phase } :=
  ⟨0, { data := [], phase := phase }, by simp [CyclicTagSystem.evaluate, cyclicTagIsHalted]⟩

/-- exactSteps 0 is identity -/
theorem CyclicTagSystem.exactStepsZero (cts : CyclicTagSystem) (cfg : CyclicTagSystemConfiguration) :
    cts.exactSteps cfg 0 = some cfg := rfl

/-- exactSteps composition: n steps then m steps = n+m steps -/
theorem CyclicTagSystem.exactStepsAdd (cts : CyclicTagSystem) (cfg cfg' : CyclicTagSystemConfiguration) (n m : Nat) :
    cts.exactSteps cfg n = some cfg' →
    cts.exactSteps cfg' m = cts.exactSteps cfg (n + m) := by
  intro h
  induction n generalizing cfg with
  | zero =>
    simp [exactSteps] at h
    rw [h]
    simp [Nat.zero_add]
  | succ n ih =>
    simp only [exactSteps] at h ⊢
    split at h
    · simp at h  -- none case
    · rename_i cfg'' h_step
      rw [Nat.succ_add]
      simp only [exactSteps, h_step]
      exact ih cfg'' h

/-- If CTS step returns some, the config was not halted -/
theorem cyclicTagSystemStepSomeNotHalted (cts : CyclicTagSystem) (cfg cfg' : CyclicTagSystemConfiguration) :
    cts.step cfg = some cfg' → cyclicTagIsHalted cfg = false := by
  intro h
  cases h_data : cfg.data with
  | nil => simp [CyclicTagSystem.step, h_data] at h
  | cons _ _ => simp [cyclicTagIsHalted, List.isEmpty, h_data]

/-- exactSteps through non-halted configs can be prepended to evaluate.
    If exactSteps cfg n = some cfg', then for any evaluate of cfg' with fuel f,
    evaluate cfg (f + n) gives the same result. -/
theorem cyclicTagSystemExactStepsPrependEvaluate (cts : CyclicTagSystem) (cfg cfg' : CyclicTagSystemConfiguration) (n fuel : Nat) :
    cts.exactSteps cfg n = some cfg' →
    cts.evaluate cfg (fuel + n) = cts.evaluate cfg' fuel := by
  intro h_nsteps
  induction n generalizing cfg with
  | zero =>
    simp [CyclicTagSystem.exactSteps] at h_nsteps
    rw [h_nsteps]; simp
  | succ n ih =>
    simp only [CyclicTagSystem.exactSteps] at h_nsteps
    split at h_nsteps
    · simp at h_nsteps
    · rename_i cfg'' h_step
      rw [Nat.add_succ]
      have h_nh := cyclicTagSystemStepSomeNotHalted cts cfg cfg'' h_step
      rw [CyclicTagSystem.evaluateStep cts cfg cfg'' (fuel + n) h_nh h_step]
      exact ih cfg'' h_nsteps

/-- If CTS reaches cfg' in n steps, and cfg' halts, then cfg halts -/
theorem cyclicTagSystemHaltsAfterExactSteps (cts : CyclicTagSystem) (cfg cfg' : CyclicTagSystemConfiguration) (n : Nat) :
    cts.exactSteps cfg n = some cfg' →
    cts.Halts cfg' →
    cts.Halts cfg := by
  intro h_nsteps ⟨fuel, result, h_eval⟩
  exact ⟨fuel + n, result, by rw [cyclicTagSystemExactStepsPrependEvaluate cts cfg cfg' n fuel h_nsteps]; exact h_eval⟩

-- ============================================================================
-- One-hot symbol processing through CTS
-- ============================================================================

/-- Helper: symbolEncode produces a non-empty list when k > 0 -/
theorem symbolEncodeNeNil (k : Nat) (hk : k > 0) (a : Fin k) :
    symbolEncode k a ≠ [] := by
  simp [symbolEncode]; omega

theorem phaseSuccMod (phase len L : Nat) :
  ((phase + 1) % L + len) % L = (phase + (len + 1)) % L := by
  calc ((phase + 1) % L + len) % L
    _ = ((phase + 1) % L + len % L) % L := by rw [Nat.add_mod ((phase + 1) % L) len L, Nat.mod_mod]
    _ = (phase + 1 + len) % L := (Nat.add_mod (phase + 1) len L).symm
    _ = (phase + (len + 1)) % L := by congr 1; omega

theorem phaseAppMod (phase a offset L : Nat) (h : a ≥ offset + 1) :
  ((phase + 1) % L + a - (offset + 1)) % L = (phase + a - offset) % L := by
  have ha : ((phase + 1) % L + a - (offset + 1)) = ((phase + 1) % L + (a - (offset + 1))) := by omega
  rw [ha]
  calc ((phase + 1) % L + (a - (offset + 1))) % L
    _ = ((phase + 1) % L + (a - (offset + 1)) % L) % L := by rw [Nat.add_mod ((phase + 1) % L) (a - (offset + 1)) L, Nat.mod_mod]
    _ = (phase + 1 + (a - (offset + 1))) % L := (Nat.add_mod (phase + 1) (a - (offset + 1)) L).symm
    _ = (phase + a - offset) % L := by congr 1; omega

theorem mapRangeSucc (a offset len : Nat) :
  (List.range (len + 1)).map (fun i => i + offset == a) =
  (offset == a) :: (List.range len).map (fun i => i + (offset + 1) == a) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  have hf : (fun i => i + offset == a) ∘ Nat.succ = fun i => i + (offset + 1) == a := by
    funext i
    have h_eq : i + 1 + offset = i + (offset + 1) := by omega
    simp [h_eq]
  rw [hf, Nat.zero_add]

theorem symbolEncodeExactStepsHelper (cts : CyclicTagSystem) (a : Nat) (len : Nat) (offset : Nat)
  (tail : List Bool) (phase : Nat) (h_phase : phase < cts.appendants.length) :
  cts.exactSteps { data := (List.range len).map (fun i => i + offset == a) ++ tail, phase := phase } len =
  some { data := tail ++ if a >= offset ∧ a < offset + len then cts.currentAppendant (phase + a - offset) else [], phase := (phase + len) % cts.appendants.length } := by
  induction len generalizing offset phase tail with
  | zero =>
    simp [CyclicTagSystem.exactSteps]
    constructor
    · intro _ h_gt
      exfalso; omega
    · exact (Nat.mod_eq_of_lt h_phase).symm
  | succ len ih =>
    rw [mapRangeSucc]
    by_cases heq : offset = a
    · have heq' : (offset == a) = true := by simp [heq]
      simp [CyclicTagSystem.exactSteps, CyclicTagSystem.step, heq']
      change cts.exactSteps { data := (List.range len).map (fun i => i + (offset + 1) == a) ++ (tail ++ cts.currentAppendant phase), phase := (phase + 1) % cts.appendants.length } len = _
      rw [ih (offset + 1) (tail ++ cts.currentAppendant phase) ((phase + 1) % cts.appendants.length)]
      · congr 1
        congr 1
        · have h1 : ¬ (a ≥ offset + 1 ∧ a < offset + 1 + len) := by omega
          have h2 : a ≥ offset ∧ a < offset + (len + 1) := by omega
          simp [h1, h2, -List.append_assoc]
          have ha : phase + a - offset = phase := by omega
          rw [ha]
        · exact phaseSuccMod phase len cts.appendants.length
      · exact Nat.mod_lt _ cts.nonempty
    · have hne' : (offset == a) = false := by simp [heq]
      simp [CyclicTagSystem.exactSteps, CyclicTagSystem.step, hne']
      rw [ih (offset + 1) tail ((phase + 1) % cts.appendants.length)]
      · congr 1
        congr 1
        · have h1 : a ≥ offset + 1 ∧ a < offset + 1 + len ↔ a ≥ offset ∧ a < offset + (len + 1) := by
            constructor <;> intro h <;> omega
          simp [h1]
          split
          · next ht =>
            have hgt : a ≥ offset + 1 := by omega
            have hidx : ((phase + 1) % cts.appendants.length + a - (offset + 1)) % cts.appendants.length = (phase + a - offset) % cts.appendants.length := phaseAppMod phase a offset cts.appendants.length hgt
            unfold CyclicTagSystem.currentAppendant
            simp [hidx]
          · rfl
        · exact phaseSuccMod phase len cts.appendants.length
      · exact Nat.mod_lt _ cts.nonempty

theorem symbolEncodeExactSteps (cts : CyclicTagSystem) (a : Nat) (len : Nat) (tail : List Bool) (phase : Nat)
  (h_phase : phase < cts.appendants.length) (h_a : a < len) :
  cts.exactSteps { data := symbolEncode len ⟨a, h_a⟩ ++ tail, phase := phase } len =
  some { data := tail ++ cts.currentAppendant (phase + a), phase := (phase + len) % cts.appendants.length } := by
  unfold symbolEncode
  have h := symbolEncodeExactStepsHelper cts a len 0 tail phase h_phase
  have h_eq : (fun (i : Nat) => i == a) = (fun i => i + 0 == a) := by funext; simp
  rw [h_eq]
  rw [h]
  have hCond : a ≥ 0 ∧ a < 0 + len := by omega
  have ha : phase + a - 0 = phase + a := by omega
  split
  · simp [ha]
  · next h_not => exfalso; exact h_not hCond

theorem CyclicTagSystem.exactStepsAddStep (cts : CyclicTagSystem) (cfg : CyclicTagSystemConfiguration) (n m : Nat) :
  cts.exactSteps cfg (n + m) = (cts.exactSteps cfg n).bind (fun c => cts.exactSteps c m) := by
  induction n generalizing cfg with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ n ih =>
    rw [Nat.succ_add]
    change (match cts.step cfg with | none => none | some c => cts.exactSteps c (n + m)) =
           (match cts.step cfg with | none => none | some c => cts.exactSteps c n).bind _
    cases h : cts.step cfg
    · rfl
    · change cts.exactSteps _ (n + m) = _
      rw [ih]

theorem tagToCyclicTagSystemAppendantFirst {k : Nat} (ts : Tag k) (hk : k > 0) (a : Fin k) :
  (tagToCyclicTagSystem ts hk).currentAppendant a.1 = tagWordEncode k (ts.productions a) := by
  unfold CyclicTagSystem.currentAppendant tagToCyclicTagSystem
  have h_lt2 : a.val < k + k := by omega
  have h_mod : a.val % (k + k) = a.val := Nat.mod_eq_of_lt h_lt2
  simp [h_mod]

theorem tagToCyclicTagSystemAppendantSecond {k : Nat} (ts : Tag k) (hk : k > 0) (b : Fin k) :
  (tagToCyclicTagSystem ts hk).currentAppendant (k + b.val) = [] := by
  unfold CyclicTagSystem.currentAppendant tagToCyclicTagSystem
  have h_lt2 : k + b.val < k + k := by omega
  have h_mod : (k + b.val) % (k + k) = k + b.val := Nat.mod_eq_of_lt h_lt2
  simp [h_mod]

-- Processing k CTS steps through a one-hot symbol:
-- Starting at phase p, with data = symbolEncode k a ++ suffix,
-- after k steps the data becomes suffix ++ (production at the triggered phase).
-- The triggered phase is (p + a.val) % (2*k).
theorem tagToCyclicTagSystemSimulation {k : Nat} (ts : Tag k) (hk : k > 0)
    (cfg : TagConfiguration k) (cfg' : TagConfiguration k) :
    ts.step cfg = some cfg' →
    (tagToCyclicTagSystem ts hk).exactSteps (tagConfigurationToCyclicTagSystem k cfg) (2 * k) =
    some (tagConfigurationToCyclicTagSystem k cfg') := by
  intro h_step
  cases cfg with
  | nil => simp [Tag.step] at h_step
  | cons a tl =>
    cases tl with
    | nil => simp [Tag.step] at h_step
    | cons b rest =>
      simp [Tag.step] at h_step

      have h_len : (tagToCyclicTagSystem ts hk).appendants.length = 2 * k := tagToCyclicTagSystemAppendantsLength ts hk
      have hk_lt : 0 < (tagToCyclicTagSystem ts hk).appendants.length := by omega
      have hk_lt2 : k < (tagToCyclicTagSystem ts hk).appendants.length := by omega

      have h_decomp : tagConfigurationToCyclicTagSystem k (a :: b :: rest) = { data := symbolEncode k a ++ (symbolEncode k b ++ tagWordEncode k rest), phase := 0 } := by rfl

      rw [h_decomp]
      have h_add : 2 * k = k + k := by omega
      rw [h_add, CyclicTagSystem.exactStepsAddStep]

      have h_step1 := symbolEncodeExactSteps (tagToCyclicTagSystem ts hk) a.val k (symbolEncode k b ++ tagWordEncode k rest) 0 hk_lt a.isLt

      have h_app1 : (tagToCyclicTagSystem ts hk).currentAppendant (0 + a.val) = tagWordEncode k (ts.productions a) := by
        have hz : 0 + a.val = a.val := by omega
        rw [hz]
        exact tagToCyclicTagSystemAppendantFirst ts hk a

      rw [h_app1] at h_step1
      have hk_lt_2k : k < 2 * k := by omega
      have hz2 : (0 + k) % (tagToCyclicTagSystem ts hk).appendants.length = k := by
        have hk0 : 0 + k = k := by omega
        rw [h_len, hk0, Nat.mod_eq_of_lt hk_lt_2k]
      rw [hz2] at h_step1
      rw [h_step1]
      simp

      have h_step2 := symbolEncodeExactSteps (tagToCyclicTagSystem ts hk) b.val k (tagWordEncode k rest ++ tagWordEncode k (ts.productions a)) k hk_lt2 b.isLt

      have h_app2 : (tagToCyclicTagSystem ts hk).currentAppendant (k + b.val) = [] := tagToCyclicTagSystemAppendantSecond ts hk b
      rw [h_app2] at h_step2

      have hz3 : (k + k) % (tagToCyclicTagSystem ts hk).appendants.length = 0 := by
        have hk2 : k + k = 2 * k := by omega
        rw [h_len, hk2, Nat.mod_self]
      rw [hz3] at h_step2
      rw [h_step2]
      rw [←h_step]
      simp [tagConfigurationToCyclicTagSystem, tagWordEncodeAppend]

/-- Tag halted means word has length 0 or 1 -/
theorem tagIsHaltedIffShort {k : Nat} (cfg : TagConfiguration k) :
    tagIsHalted cfg = true ↔ cfg.length < 2 := by
  simp [tagIsHalted]

-- ============================================================================
-- Forward halting direction
-- ============================================================================

/-- A tag system halts completely empty if it evaluates to [] -/
def Tag.HaltsEmpty {k : Nat} (ts : Tag k) (cfg : TagConfiguration k) : Prop :=
  ∃ fuel, ts.evaluate cfg fuel = some []

/-- Forward: Tag halts unconditionally full -> CTS halts.
    If tag evaluate reaches an empty configuration, the CTS also halts. -/
theorem tagToCyclicTagSystemHaltingForward {k : Nat} (ts : Tag k) (hk : k > 0)
    (cfg : TagConfiguration k) :
    ts.HaltsEmpty cfg → (tagToCyclicTagSystem ts hk).Halts (tagConfigurationToCyclicTagSystem k cfg) := by
  intro ⟨fuel, h_eval⟩
  induction fuel generalizing cfg with
  | zero =>
    simp [Tag.evaluate] at h_eval
    obtain ⟨hh, heq⟩ := h_eval
    subst heq
    exact cyclicTagSystemHaltsOnEmpty _ _
  | succ n ih =>
    simp [Tag.evaluate] at h_eval
    by_cases hh : tagIsHalted cfg = true
    · simp [hh] at h_eval
      subst h_eval
      exact cyclicTagSystemHaltsOnEmpty _ _
    · simp [hh] at h_eval
      cases h_step_eq : ts.step cfg with
      | none =>
        have := (Tag.stepNoneIffHalted ts cfg).mp h_step_eq
        simp [this] at hh
      | some cfg' =>
        simp [h_step_eq] at h_eval
        have ⟨fuel', result', he⟩ := ih cfg' h_eval
        have h_sim := tagToCyclicTagSystemSimulation ts hk cfg cfg' h_step_eq
        exact cyclicTagSystemHaltsAfterExactSteps _ _ _ _ h_sim ⟨fuel', result', he⟩

/-- Helper for tag halting proof -/
theorem Tag.notHaltedExistsThree {k : Nat} {cfg : TagConfiguration k} (h : tagIsHalted cfg = false) :
    ∃ a b rest, cfg = a :: b :: rest := by
  cases cfg with
  | nil => simp [tagIsHalted] at h
  | cons a tl =>
    cases tl with
    | nil => simp [tagIsHalted] at h
    | cons b rest => exact ⟨a, b, rest, rfl⟩

theorem cyclicTagSystemStepNoneIffHalted (cts : CyclicTagSystem) (cfg : CyclicTagSystemConfiguration) :
    cts.step cfg = none ↔ cyclicTagIsHalted cfg = true := by
  dsimp [CyclicTagSystem.step, cyclicTagIsHalted]
  cases cfg.data <;> simp

/-- If CTS has data of length L, it cannot halt in fewer than L steps. -/
theorem cyclicTagSystemEvaluateNoneOfLength {cts : CyclicTagSystem} {cfg : CyclicTagSystemConfiguration} {f : Nat} :
    f < cfg.data.length → cts.evaluate cfg f = none := by
  induction f generalizing cfg with
  | zero =>
    intro h
    unfold CyclicTagSystem.evaluate
    split <;> rename_i h_h
    · simp [cyclicTagIsHalted] at h_h
      rw [h_h] at h; simp at h
    · rfl
  | succ f ih =>
    intro h
    unfold CyclicTagSystem.evaluate
    split <;> rename_i h_h
    · simp [cyclicTagIsHalted] at h_h
      rw [h_h] at h; simp at h
    · cases h_st : cts.step cfg with
      | none =>
        have h_halt := (cyclicTagSystemStepNoneIffHalted cts cfg).mp h_st
        rw [h_halt] at h_h
        contradiction
      | some cfg' =>
        have h_len : cfg'.data.length ≥ cfg.data.length - 1 := by
          cases h_c : cfg.data with
          | nil => simp [CyclicTagSystem.step, h_c] at h_st
          | cons head rest =>
            simp [CyclicTagSystem.step, h_c] at h_st
            subst h_st
            cases head <;> (try simp) <;> (try omega)
        exact ih (by omega)

-- ============================================================================
-- Backward direction: CyclicTagSystem halts -> Tag halts
-- ============================================================================

theorem cyclicTagSystemToTagHalting {k : Nat} (ts : Tag k) (hk : k > 0)
    (cfg : TagConfiguration k) :
    (tagToCyclicTagSystem ts hk).Halts (tagConfigurationToCyclicTagSystem k cfg) → ts.Halts cfg := by
  intro ⟨fuel, result, h_eval⟩
  induction fuel using Nat.strongRecOn generalizing cfg result with
  | ind n ih =>
    cases h_h : cyclicTagIsHalted (tagConfigurationToCyclicTagSystem k cfg) with
    | true =>
      -- CTS is halted
      have h_cfg_nil : cfg = [] := by
        simp [cyclicTagIsHalted, tagConfigurationToCyclicTagSystem] at h_h
        have h_len_mul := tagWordEncodeLength k cfg
        rw [h_h] at h_len_mul
        simp at h_len_mul
        cases h_len : cfg.length with
        | zero => exact List.eq_nil_of_length_eq_zero h_len
        | succ n =>
          rw [h_len] at h_len_mul
          have h_pos : k * (n + 1) > 0 := Nat.mul_pos hk (Nat.succ_pos n)
          rw [h_len_mul] at h_pos
          omega
      subst h_cfg_nil
      exact ⟨0, [], by simp [Tag.evaluate, tagIsHalted]⟩
    | false =>
      -- CTS is not halted
      have h_eval_orig := h_eval
      unfold CyclicTagSystem.evaluate at h_eval
      rw [h_h] at h_eval
      cases n with
      | zero => contradiction
      | succ n' =>
        -- fuel = n' + 1
        cases h_st : (tagToCyclicTagSystem ts hk).step (tagConfigurationToCyclicTagSystem k cfg) with
        | none =>
          -- Should not happen since not halted
          have := (cyclicTagSystemStepNoneIffHalted _ _).mp h_st
          rw [this] at h_h; contradiction
        | some cfg_next =>
          rw [h_st] at h_eval
          cases hh : tagIsHalted cfg with
          | true => exact ⟨0, cfg, by simp [Tag.evaluate, hh]⟩
          | false =>
            -- Not halted, so it has at least 2 symbols
            obtain ⟨a, b, rest, h_cfg_s⟩ := Tag.notHaltedExistsThree hh
            subst h_cfg_s
            let cfg_s : TagConfiguration k := a :: b :: rest
            let cfg' := rest ++ ts.productions a
            have h_step : ts.step cfg_s = some cfg' := by
              simp [Tag.step, cfg_s, cfg']
            have h_sim := tagToCyclicTagSystemSimulation ts hk cfg_s cfg' h_step
            -- If fuel is not enough to process 2k steps, it can't halt
            by_cases h_fuel : n' + 1 < 2 * k
            · have h_none : (tagToCyclicTagSystem ts hk).evaluate (tagConfigurationToCyclicTagSystem k cfg_s) (n' + 1) = none := by
                apply cyclicTagSystemEvaluateNoneOfLength
                unfold tagConfigurationToCyclicTagSystem
                rw [tagWordEncodeLength]
                have h_le_2 : 2 ≤ cfg_s.length := by simp [cfg_s]
                have h_le_mul : 2 * k ≤ k * cfg_s.length := by
                  rw [Nat.mul_comm]
                  apply Nat.mul_le_mul_left k h_le_2
                omega
              rw [h_none] at h_eval_orig; contradiction
            · -- Enough fuel to process 2k steps (n' + 1 >= 2k)
              have h_nsteps : (tagToCyclicTagSystem ts hk).exactSteps (tagConfigurationToCyclicTagSystem k cfg_s) (2 * k) = some (tagConfigurationToCyclicTagSystem k cfg') := h_sim
              have h_eval' : (tagToCyclicTagSystem ts hk).evaluate (tagConfigurationToCyclicTagSystem k cfg') (n' + 1 - 2 * k) = some result := by
                rw [← cyclicTagSystemExactStepsPrependEvaluate (tagToCyclicTagSystem ts hk) (tagConfigurationToCyclicTagSystem k cfg_s) (tagConfigurationToCyclicTagSystem k cfg') (2 * k) (n' + 1 - 2 * k) h_nsteps]
                rw [Nat.sub_add_cancel (by omega)]
                exact h_eval_orig
              have ⟨f', r', he⟩ := ih (n' + 1 - 2 * k) (by omega) cfg' result h_eval'
              exact ⟨f' + 1, r', by rw [Tag.evaluateStep ts cfg_s cfg' f' (by simp [tagIsHalted, cfg_s]) h_step, he]⟩

-- ============================================================================
-- Verification examples
-- ============================================================================

/-- Example 2-tag system with k=2 -/
def exampleTag2 : Tag 2 where
  productions := fun i =>
    match i with
    | ⟨0, _⟩ => [⟨1, by omega⟩, ⟨0, by omega⟩]  -- 0 -> [1, 0]
    | ⟨1, _⟩ => [⟨0, by omega⟩]                    -- 1 -> [0]
    | ⟨_, _⟩ => []

theorem symbolEncode20 : symbolEncode 2 ⟨0, by omega⟩ = [true, false] := by native_decide
theorem symbolEncode21 : symbolEncode 2 ⟨1, by omega⟩ = [false, true] := by native_decide

theorem tagWordEncode01 :
    tagWordEncode 2 [⟨0, by omega⟩, ⟨1, by omega⟩] = [true, false, false, true] := by
  native_decide

theorem tagToCyclicTagSystemAppendants :
    (tagToCyclicTagSystem exampleTag2 (by omega)).appendants =
    [[false, true, true, false], [true, false], [], []] := by
  native_decide

-- ============================================================================
-- Simulation verification (native_decide)
-- ============================================================================

-- Verify the corrected CTS (2k appendants) simulates correctly.
-- Tag step on [0, 1, 0] -> [0] ++ productions(0) = [0, 1, 0] (fixed point)
-- 2k = 4 CTS steps on encoded [0,1,0] should yield encoded [0,1,0]

def exampleCyclicTagSystemFromTag := tagToCyclicTagSystem exampleTag2 (by omega)
def exampleCyclicTagSystemInitial2 := tagConfigurationToCyclicTagSystem 2
    [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]

/-- Key verification: 4 CTS steps (= 2*k = 2*2) on encoded [0,1,0]
    produces exactly the encoding of the tag step result [0,1,0].
    Confirms corrected 2k-appendant CTS construction. -/
theorem simulationExampleCorrected :
    exampleCyclicTagSystemFromTag.exactSteps exampleCyclicTagSystemInitial2 4 =
    some (tagConfigurationToCyclicTagSystem 2 [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]) := by
  native_decide

/-- Verify [1, 0, 1] -> [1] ++ productions(1) = [1, 0] -/
theorem simulationExample2 :
    exampleCyclicTagSystemFromTag.exactSteps
      (tagConfigurationToCyclicTagSystem 2 [⟨1, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]) 4 =
    some (tagConfigurationToCyclicTagSystem 2 [⟨1, by omega⟩, ⟨0, by omega⟩]) := by
  native_decide

/-- Verify [0, 0, 1, 1] -> [1, 1] ++ productions(0) = [1, 1, 1, 0] -/
theorem simulationExample3 :
    exampleCyclicTagSystemFromTag.exactSteps
      (tagConfigurationToCyclicTagSystem 2 [⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩]) 4 =
    some (tagConfigurationToCyclicTagSystem 2 [⟨1, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]) := by
  native_decide

-- ============================================================================
-- Generic Simulation instance (Cook's encoding, Tag → CTS)
-- ============================================================================

/-- One tag step corresponds to 2k CTS steps, lifted to `iterationStep`. -/
theorem tagToCTSCommutes {k : Nat} (ts : Tag k) (hk : k > 0)
    (config config' : TagConfiguration k)
    (h_step : ts.step config = some config') :
    ∃ n, (CyclicTagSystem.toComputationalMachine (tagToCyclicTagSystem ts hk)).iterationStep n
      (tagConfigurationToCyclicTagSystem k config) =
      some (tagConfigurationToCyclicTagSystem k config') :=
  ⟨2 * k, by
    rw [CyclicTagSystem.iterationStep_eq_exactSteps]
    exact tagToCyclicTagSystemSimulation ts hk config config' h_step⟩

/- Tag → CTS as a `Simulation`: assembled directly in `Lean/Edges.lean`
   (`UniversalityGraph.edge_TagtoCTS`). The `halting` field of that simulation is
   not provable from `tagToCTSCommutes` alone, because Cook's CTS encoding does
   not preserve halting on single-element tag words: encode `[a]` is `k` bits
   and the CTS only halts on this configuration when `productions a` is empty.
   The edge wrapper therefore takes an explicit hypothesis
     `hHalt : ∀ cfg, ts.step cfg = none → CTS.Halts (encode cfg)`
   which holds for the tag systems that arise in Cocke-Minsky-style universality
   constructions (where halting goes through the empty word). The standalone
   simulation has been intentionally omitted to keep this conditionality
   visible in the edge's type. -/

end TagSystem
