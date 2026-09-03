import Submission.BilinearExplore

/-! An exact residue-root formula for the remaining bilinear discrepancy.
This identifies the reciprocal-residue statistic whose weighted cancellation
would be needed; it does not assert that cancellation. -/

namespace Erdos371

/-- The residue `m` with `a ∣ m` and `b ∣ m + 1`. -/
def adjacentRoot (a b : ℕ) (hab : a.Coprime b) : ℕ :=
  (Nat.chineseRemainder hab 0 (b - 1)).val

lemma adjacentRoot_dvd_left (a b : ℕ) (hab : a.Coprime b) :
    a ∣ adjacentRoot a b hab :=
  Nat.modEq_zero_iff_dvd.mp (Nat.chineseRemainder hab 0 (b - 1)).property.1

lemma adjacentRoot_dvd_right (a b : ℕ) (hab : a.Coprime b) (hb : 0 < b) :
    b ∣ adjacentRoot a b hab + 1 := by
  have h := (Nat.chineseRemainder hab 0 (b - 1)).property.2.add_right 1
  rw [Nat.sub_add_cancel hb] at h
  exact (h.dvd_iff (dvd_refl b)).mpr (dvd_refl b)

lemma adjacentRoot_lt (a b : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    adjacentRoot a b hab < a * b :=
  Nat.chineseRemainder_lt_mul hab 0 (b - 1) ha.ne' hb.ne'

lemma adjacentRoot_pos (a b : ℕ) (hab : a.Coprime b) (hb : 1 < b) :
    0 < adjacentRoot a b hab := by
  have h := adjacentRoot_dvd_right a b hab (by omega)
  by_contra h'
  have hz : adjacentRoot a b hab = 0 := by omega
  rw [hz, zero_add] at h
  have := Nat.dvd_one.mp h
  omega

lemma adjacentRoot_unique (a b : ℕ) (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (m : ℕ) (hm : m < a * b) (ham : a ∣ m) (hbm : b ∣ m + 1) :
    m = adjacentRoot a b hab := by
  have h₁ : Nat.ModEq a m (adjacentRoot a b hab) :=
    ham.modEq_zero_nat.trans (adjacentRoot_dvd_left a b hab).zero_modEq_nat
  have h₂ : Nat.ModEq b m (adjacentRoot a b hab) :=
    (hbm.modEq_zero_nat.trans (adjacentRoot_dvd_right a b hab hb).zero_modEq_nat).add_right_cancel' 1
  exact ((Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨h₁, h₂⟩).eq_of_lt_of_lt hm
    (adjacentRoot_lt a b hab ha hb)

/-- The reciprocal residues are reflected around `a*b - 1`. -/
theorem adjacentRoot_swap (a b : ℕ) (hab : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    adjacentRoot b a hab.symm = a * b - 1 - adjacentRoot a b hab := by
  have hr := adjacentRoot_lt a b hab (by omega) (by omega)
  have hsum : adjacentRoot a b hab + (a * b - 1 - adjacentRoot a b hab) + 1 = a * b := by omega
  have h₁ := reflected_divisibility a (adjacentRoot a b hab)
    (a * b - 1 - adjacentRoot a b hab) (by rw [hsum]; exact Nat.dvd_mul_right a b)
  have h₂ := reflected_divisibility b (adjacentRoot a b hab)
    (a * b - 1 - adjacentRoot a b hab) (by rw [hsum]; exact Nat.dvd_mul_left b a)
  symm
  apply adjacentRoot_unique b a hab.symm (by omega) (by omega)
  · rw [Nat.mul_comm b a]
    omega
  · exact h₂.1.mpr (adjacentRoot_dvd_right a b hab (by omega))
  · exact h₁.2.mpr (adjacentRoot_dvd_left a b hab)

theorem adjacentRoot_reciprocity (a b : ℕ) (hab : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    adjacentRoot a b hab + adjacentRoot b a hab.symm + 1 = a * b := by
  rw [adjacentRoot_swap a b hab ha hb]
  have h := adjacentRoot_lt a b hab (by omega) (by omega)
  omega

/-- Dividing out the prescribed factors gives the usual reciprocal-residue
identity. Both fractions lie strictly between zero and one. -/
theorem adjacentRoot_fraction_reciprocity (a b : ℕ) (hab : a.Coprime b)
    (ha : 1 < a) (hb : 1 < b) :
    ((adjacentRoot a b hab / a : ℕ) : ℝ) / b +
      ((adjacentRoot b a hab.symm / b : ℕ) : ℝ) / a + 1 / ((a : ℝ) * b) = 1 := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have h₁ : (a : ℝ) * ((adjacentRoot a b hab / a : ℕ) : ℝ) = adjacentRoot a b hab := by
    exact_mod_cast Nat.mul_div_cancel' (adjacentRoot_dvd_left a b hab)
  have h₂ : (b : ℝ) * ((adjacentRoot b a hab.symm / b : ℕ) : ℝ) = adjacentRoot b a hab.symm := by
    exact_mod_cast Nat.mul_div_cancel' (adjacentRoot_dvd_left b a hab.symm)
  have he : (adjacentRoot a b hab : ℝ) + adjacentRoot b a hab.symm + 1 = (a : ℝ) * b := by
    exact_mod_cast adjacentRoot_reciprocity a b hab ha hb
  field_simp
  nlinarith

lemma bilinearIndex_unique (a b : ℕ) (hab : a.Coprime b) (ha : 1 < a) (hb : 1 < b)
    (n : ℕ) (hn : n < a * b) (han : a ∣ n + 1) (hbn : b ∣ n + 2) :
    n = adjacentRoot a b hab - 1 := by
  have hpos := adjacentRoot_pos a b hab hb
  have hlt := adjacentRoot_lt a b hab (by omega) (by omega)
  have h₁ : a ∣ (adjacentRoot a b hab - 1) + 1 := by
    rw [Nat.sub_add_cancel hpos]
    exact adjacentRoot_dvd_left a b hab
  have h₂ : b ∣ (adjacentRoot a b hab - 1) + 2 := by
    convert adjacentRoot_dvd_right a b hab (by omega) using 1; omega
  have hm₁ : Nat.ModEq a n (adjacentRoot a b hab - 1) :=
    (han.modEq_zero_nat.trans h₁.zero_modEq_nat).add_right_cancel' 1
  have hm₂ : Nat.ModEq b n (adjacentRoot a b hab - 1) :=
    (hbn.modEq_zero_nat.trans h₂.zero_modEq_nat).add_right_cancel' 2
  exact ((Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hm₁, hm₂⟩).eq_of_lt_of_lt hn (by omega)

lemma bilinearCount_short_eq_indicator (N a b : ℕ) (hab : a.Coprime b)
    (ha : 1 < a) (hb : 1 < b) (hN : N ≤ a * b) :
    bilinearCount N a b = if adjacentRoot a b hab ≤ N then 1 else 0 := by
  have hpos := adjacentRoot_pos a b hab hb
  by_cases h : adjacentRoot a b hab ≤ N
  · rw [if_pos h]
    apply le_antisymm (bilinearCount_le_one N a b hab hN)
    apply Nat.succ_le_iff.mpr
    apply Finset.card_pos.mpr
    refine ⟨adjacentRoot a b hab - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩⟩
    · rw [Nat.sub_add_cancel hpos]
      exact adjacentRoot_dvd_left a b hab
    · convert adjacentRoot_dvd_right a b hab (by omega) using 1; omega
  · rw [if_neg h]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnN, han, hbn⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    have he := bilinearIndex_unique a b hab ha hb n (hnN'.trans_le hN) han hbn
    omega

lemma bilinearCount_discrepancy_mod (N a b : ℕ) :
    (bilinearCount N a b : ℝ) - bilinearCount N b a =
      (bilinearCount (N % (a * b)) a b : ℝ) - bilinearCount (N % (a * b)) b a := by
  have hp : Function.Periodic (fun n => pairIndicatorDifference a b (n + 1)) (a * b) := by
    intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      pairIndicatorDifference_periodic a b (n + 1)
  rw [bilinearCount_difference_eq_sum, periodic_sum_zero_eq_remainder _ (a * b) hp
    (pairIndicatorDifference_shifted_mean_zero a b), ← bilinearCount_difference_eq_sum]

/-- The exact discrepancy is a difference of two reciprocal-root indicators.
Bounding each indicator separately loses the cancellation still needed after
summing with the Möbius/least-factor weights. -/
theorem bilinearCount_discrepancy_root_formula (N a b : ℕ) (hab : a.Coprime b)
    (ha : 1 < a) (hb : 1 < b) :
    (bilinearCount N a b : ℝ) - bilinearCount N b a =
      (if adjacentRoot a b hab ≤ N % (a * b) then 1 else 0) -
      (if a * b - 1 - adjacentRoot a b hab ≤ N % (a * b) then 1 else 0) := by
  rw [bilinearCount_discrepancy_mod]
  have hN : N % (a * b) ≤ a * b := (Nat.mod_lt N (by positivity)).le
  rw [bilinearCount_short_eq_indicator _ a b hab ha hb hN,
    bilinearCount_short_eq_indicator _ b a hab.symm hb ha (by simpa [Nat.mul_comm] using hN),
    adjacentRoot_swap a b hab ha hb]
  push_cast
  rfl

/-- Even for prime arguments in increasing order, the discrepancy can have
either sign. These are finite checks, not a counterexample to Erdős 371. -/
theorem prime_pair_discrepancy_both_signs :
    (bilinearCount 15 5 7 : ℤ) - bilinearCount 15 7 5 = -1 ∧
    (bilinearCount 15 5 11 : ℤ) - bilinearCount 15 11 5 = 1 := by
  decide +kernel

#print axioms adjacentRoot_reciprocity
#print axioms adjacentRoot_fraction_reciprocity
#print axioms bilinearCount_discrepancy_root_formula
#print axioms prime_pair_discrepancy_both_signs
end Erdos371
