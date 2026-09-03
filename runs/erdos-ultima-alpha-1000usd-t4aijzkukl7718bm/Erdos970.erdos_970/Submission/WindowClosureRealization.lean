import Submission.WindowConstraintClosure

/-! Binary-word realizations of the exact signed-distance closure. -/

namespace Erdos970.WindowConstraintClosure
open IntervalRescaling.IntegerHull

def signedDistance (l u : ℕ → ℤ) (z : ℤ) : ℤ :=
  -twoSidedCumulative l u (-z)

lemma signedDistance_nat {l u : ℕ → ℤ} (hl : l 0 = 0) (hu : u 0 = 0) (n : ℕ) :
    signedDistance l u n = u n := by
  simp only [signedDistance, twoSidedCumulative_neg_nat l u hl hu, neg_neg]

lemma signedDistance_neg_nat (l u : ℕ → ℤ) (n : ℕ) :
    signedDistance l u (-(n : ℤ)) = -l n := by
  simp only [signedDistance, neg_neg, twoSidedCumulative_nat]

/-- The four compatibility inequalities are precisely the signed triangle
inequalities for the reflected cumulative profile. -/
theorem signedDistance_isDistance {l u : ℕ → ℤ}
    (h : Compatible (fun n => (l n : ℝ)) (fun n => (u n : ℝ))) :
    IsDistance (signedDistance l u) := by
  have hl0 : l 0 = 0 := by exact_mod_cast h.lower_zero
  have hu0 : u 0 = 0 := by exact_mod_cast h.upper_zero
  constructor
  · simp [signedDistance, twoSidedCumulative, hl0]
  · intro x y
    cases y with
    | ofNat n =>
      change signedDistance l u (x + (n : ℤ)) ≤ _ + signedDistance l u (n : ℤ)
      rw [signedDistance_nat hl0 hu0]
      have hh := (h.twoSided_increments (-(x + (n : ℤ))) n).2
      have he : -(x + (n : ℤ)) + n = -x := by ring
      rw [he] at hh
      simp only [signedDistance]
      omega
    | negSucc n =>
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
      rw [hn, signedDistance_neg_nat]
      have hh := (h.twoSided_increments (-x) (n + 1)).1
      have he : -(x + -((n + 1 : ℕ) : ℤ)) = -x + ((n + 1 : ℕ) : ℤ) := by ring
      simp only [signedDistance]
      rw [he]
      omega

lemma intWordCount_cons (w : ℤ → Bool) (a : ℤ) (n : ℕ) :
    intWordCount w a (n + 1) = (if w a then 1 else 0) + intWordCount w (a + 1) n := by
  simp only [intWordCount, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show a + ((i : ℤ) + 1) = a + 1 + (i : ℤ) by ring]

/-- Signed indefinite count of an arbitrary bi-infinite binary word. -/
def wordCumulative (w : ℤ → Bool) (a : ℤ) : ℤ :=
  if 0 ≤ a then (intWordCount w 0 a.toNat : ℤ)
  else -(intWordCount w a (-a).toNat : ℤ)

lemma wordCumulative_nat (w : ℤ → Bool) (n : ℕ) :
    wordCumulative w n = intWordCount w 0 n := by
  simp [wordCumulative]

lemma wordCumulative_neg_nat (w : ℤ → Bool) (n : ℕ) :
    wordCumulative w (-(n : ℤ)) = -(intWordCount w (-(n : ℤ)) n : ℤ) := by
  cases n with
  | zero => simp [wordCumulative, intWordCount]
  | succ n =>
    rw [wordCumulative, if_neg (by omega)]
    simp only [neg_neg, Int.toNat_natCast]

lemma wordCumulative_step (w : ℤ → Bool) (a : ℤ) :
    wordCumulative w (a + 1) - wordCumulative w a = if w a then 1 else 0 := by
  cases a with
  | ofNat n =>
    change wordCumulative w ((n : ℤ) + 1) - wordCumulative w (n : ℤ) = _
    rw [← Nat.cast_one, ← Nat.cast_add, wordCumulative_nat, wordCumulative_nat,
      intWordCount_succ]
    simp
  | negSucc n =>
    have ha : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    have he : Int.negSucc n + 1 = -(n : ℤ) := by omega
    rw [he, ha, wordCumulative_neg_nat, wordCumulative_neg_nat, intWordCount_cons]
    have he' : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
    rw [he']
    simp

lemma wordCumulative_steps (w : ℤ → Bool) (a : ℤ) :
    0 ≤ wordCumulative w (a + 1) - wordCumulative w a ∧
      wordCumulative w (a + 1) - wordCumulative w a ≤ 1 := by
  rw [wordCumulative_step]
  split <;> omega

lemma wordCumulative_word (w : ℤ → Bool) : intStepWord (wordCumulative w) = w := by
  funext a
  have hh := wordCumulative_step w a
  cases hw : w a <;> simp only [hw, Bool.false_eq_true, if_false, if_true] at hh
  · have hle : ¬wordCumulative w a < wordCumulative w (a + 1) := by omega
    simp [intStepWord, hle]
  · have hlt : wordCumulative w a < wordCumulative w (a + 1) := by omega
    simp [intStepWord, hlt]

lemma wordCumulative_count (w : ℤ → Bool) (a : ℤ) (n : ℕ) :
    (intWordCount w a n : ℤ) = wordCumulative w (a + n) - wordCumulative w a := by
  rw [← intWordCount_intStepWord (wordCumulative w) (wordCumulative_steps w),
    wordCumulative_word]

lemma admissible_wordCumulative_iff {d : ℤ → ℤ} {w : ℤ → Bool} :
    Admissible d (wordCumulative w) ↔
      ∀ (a : ℤ) (n : ℕ), -d (-(n : ℤ)) ≤ (intWordCount w a n : ℤ) ∧
        (intWordCount w a n : ℤ) ≤ d n := by
  constructor
  · intro h a n
    rw [wordCumulative_count]
    have h₁ := h a n
    have h₂ := h (a + n) (-(n : ℤ))
    simp only [add_neg_cancel_right] at h₂
    omega
  · intro h a z
    cases z with
    | ofNat n => simpa only [wordCumulative_count] using (h a n).2
    | negSucc n =>
      have he : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
      rw [he]
      have hh := (h (a + -((n + 1 : ℕ) : ℤ)) (n + 1)).1
      rw [wordCumulative_count] at hh
      simp only [neg_add_cancel_right] at hh
      omega

/-- Reflected distance realizes all lower initial counts. -/
def reflected (d : ℤ → ℤ) (a : ℤ) : ℤ := -d (-a)

lemma IsDistance.reflected_admissible {d : ℤ → ℤ} (hd : IsDistance d) :
    Admissible d (reflected d) := by
  intro a z
  have hh := hd.subadd (-(a + z)) z
  rw [show -(a + z) + z = -a by ring] at hh
  simp only [reflected]
  omega

lemma Admissible.lowerBlock {d F : ℤ → ℤ} {g b : ℤ}
    (h : Admissible d F) (hb : d (-g) ≤ -b) : LowerBlock F g b := by
  intro a
  have hh := h (a + g) (-g)
  simp only [add_neg_cancel_right] at hh
  omega

lemma Admissible.unit_steps {d F : ℤ → ℤ}
    (h : Admissible d F) (hl : d (-1) ≤ 0) (hu : d 1 ≤ 1) (a : ℤ) :
    0 ≤ F (a + 1) - F a ∧ F (a + 1) - F a ≤ 1 := by
  have h₁ := h a 1
  have h₂ := h (a + 1) (-1)
  simp only [add_neg_cancel_right] at h₂
  omega

/-- Both extremal initial counts have actual binary-word witnesses for the
signed window constraints. Neither witness is asserted to be a residue word. -/
theorem IsDistance.binary_realizations {d : ℤ → ℤ}
    (hd : IsDistance d) (hl : d (-1) ≤ 0) (hu : d 1 ≤ 1) :
    (∃ w : ℤ → Bool, Admissible d (wordCumulative w) ∧
      ∀ n : ℕ, (intWordCount w 0 n : ℤ) = d n) ∧
    (∃ w : ℤ → Bool, Admissible d (wordCumulative w) ∧
      ∀ n : ℕ, (intWordCount w 0 n : ℤ) = -d (-(n : ℤ))) := by
  have make (F : ℤ → ℤ) (hF : Admissible d F) (hzero : F 0 = 0) :
      ∃ w : ℤ → Bool, Admissible d (wordCumulative w) ∧
        ∀ n : ℕ, (intWordCount w 0 n : ℤ) = F n := by
    have hs := hF.unit_steps hl hu
    refine ⟨intStepWord F, ?_, ?_⟩
    · apply admissible_wordCumulative_iff.mpr
      intro a n
      rw [intWordCount_intStepWord F hs]
      have h₁ := hF a n
      have h₂ := hF (a + n) (-(n : ℤ))
      simp only [add_neg_cancel_right] at h₂
      omega
    · intro n
      simp only [intWordCount_intStepWord F hs, zero_add, hzero, sub_zero]
  constructor
  · exact make d hd.admissible hd.zero
  · exact make (reflected d) hd.reflected_admissible (by simp [reflected, hd.zero])

/-- A binary word obeying the old signed window constraints and the new block
lower bound. -/
def WordModel (d : ℤ → ℤ) (g : ℕ) (b : ℤ) (w : ℤ → Bool) : Prop :=
  Admissible d (wordCumulative w) ∧ LowerBlock (wordCumulative w) g b

lemma wordModel_iff_counts {d : ℤ → ℤ} {g : ℕ} {b : ℤ} {w : ℤ → Bool} :
    WordModel d g b w ↔
      (∀ (a : ℤ) (n : ℕ), -d (-(n : ℤ)) ≤ (intWordCount w a n : ℤ) ∧
        (intWordCount w a n : ℤ) ≤ d n) ∧
      ∀ a, b ≤ (intWordCount w a g : ℤ) := by
  simp only [WordModel, admissible_wordCumulative_iff, LowerBlock, wordCumulative_count]

/-- Exact equivalence of word models, rather than only sound propagation. -/
theorem wordModel_iff_closed {d F : ℤ → ℤ} {g : ℕ} {b : ℤ}
    (hd : IsDistance d) (hF : Admissible d F) (hB : LowerBlock F g b)
    (w : ℤ → Bool) :
    WordModel d g b w ↔ Admissible (addLower d g b) (wordCumulative w) := by
  constructor
  · rintro ⟨hw, hb⟩
    exact admissible_addLower hw hb
  · intro hw
    exact ⟨fun a z => (hw a z).trans (addLower_le hF hB z),
      hw.lowerBlock (addLower_neg_block hd hF hB)⟩

/-- No stronger lower window count follows from the old constraints and the
new block bound, even when every integer translate is enforced. -/
theorem window_lower_iff {d F : ℤ → ℤ} {g : ℕ} {b : ℤ}
    (hd : IsDistance d) (hl : d (-1) ≤ 0) (hu : d 1 ≤ 1)
    (hF : Admissible d F) (hB : LowerBlock F g b) (n : ℕ) (v : ℤ) :
    (∀ w : ℤ → Bool, WordModel d g b w → v ≤ (intWordCount w 0 n : ℤ)) ↔
      v ≤ -addLower d g b (-(n : ℤ)) := by
  have he := hd.addLower hF hB
  have hel := (addLower_le hF hB (-1)).trans hl
  have heu := (addLower_le hF hB 1).trans hu
  constructor
  · intro hall
    obtain ⟨w, hw, heq⟩ := (he.binary_realizations hel heu).2
    have hh := hall w ((wordModel_iff_closed hd hF hB w).mpr hw)
    simpa only [heq n] using hh
  · intro hv w hw
    have hh := (admissible_wordCumulative_iff.mp
      ((wordModel_iff_closed hd hF hB w).mp hw) 0 n).1
    exact hv.trans hh

/-- Likewise the upper closure bound is attained by a binary model. -/
theorem window_upper_iff {d F : ℤ → ℤ} {g : ℕ} {b : ℤ}
    (hd : IsDistance d) (hl : d (-1) ≤ 0) (hu : d 1 ≤ 1)
    (hF : Admissible d F) (hB : LowerBlock F g b) (n : ℕ) (v : ℤ) :
    (∀ w : ℤ → Bool, WordModel d g b w → (intWordCount w 0 n : ℤ) ≤ v) ↔
      addLower d g b n ≤ v := by
  have he := hd.addLower hF hB
  have hel := (addLower_le hF hB (-1)).trans hl
  have heu := (addLower_le hF hB 1).trans hu
  constructor
  · intro hall
    obtain ⟨w, hw, heq⟩ := (he.binary_realizations hel heu).1
    have hh := hall w ((wordModel_iff_closed hd hF hB w).mpr hw)
    simpa only [heq n] using hh
  · intro hv w hw
    have hh := (admissible_wordCumulative_iff.mp
      ((wordModel_iff_closed hd hF hB w).mp hw) 0 n).2
    exact hh.trans hv

/-- An empty interval is possible in the binary-word relaxation exactly when the
closed lower count is zero. This is NOT a prime-residue cover construction. -/
theorem empty_window_iff {d F : ℤ → ℤ} {g : ℕ} {b : ℤ}
    (hd : IsDistance d) (hl : d (-1) ≤ 0) (hu : d 1 ≤ 1)
    (hF : Admissible d F) (hB : LowerBlock F g b) (n : ℕ) :
    (∃ w : ℤ → Bool, WordModel d g b w ∧ intWordCount w 0 n = 0) ↔
      addLower d g b (-(n : ℤ)) = 0 := by
  have he := hd.addLower hF hB
  have hel := (addLower_le hF hB (-1)).trans hl
  have heu := (addLower_le hF hB 1).trans hu
  obtain ⟨v, hv, heq⟩ := (he.binary_realizations hel heu).2
  constructor
  · rintro ⟨w, hw, hzero⟩
    have hh := (admissible_wordCumulative_iff.mp
      ((wordModel_iff_closed hd hF hB w).mp hw) 0 n).1
    rw [hzero, Nat.cast_zero] at hh
    have hvn := heq n
    have hn := Int.natCast_nonneg (intWordCount v 0 n)
    omega
  · intro hz
    refine ⟨v, (wordModel_iff_closed hd hF hB v).mpr hv, ?_⟩
    have hh := heq n
    rw [hz, neg_zero] at hh
    exact_mod_cast hh

#print axioms signedDistance_isDistance
#print axioms IsDistance.binary_realizations
#print axioms wordModel_iff_closed
#print axioms window_lower_iff
#print axioms window_upper_iff
#print axioms empty_window_iff
end Erdos970.WindowConstraintClosure
