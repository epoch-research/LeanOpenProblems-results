import Submission.BilinearExplore

/-! Exact cancellation along complete rows of the rough bilinear expansion. -/

namespace Erdos371

noncomputable def leastOrderSign (a p : ℕ) : ℝ :=
  if a.minFac < p then -1 else if p < a.minFac then 1 else 0

lemma leastOrderSign_norm_le (a p : ℕ) : ‖leastOrderSign a p‖ ≤ 1 := by
  unfold leastOrderSign
  split_ifs <;> norm_num

/-- Above this threshold the product cutoff imposes no further restriction on
an admissible rough factor in the other coordinate. -/
lemma roughBilinearWeight_large_row (B D a b : ℕ) (ha : 1 < a) (hBa : B < a.minFac)
    (hD : D < a * (B + 1)) :
    roughBilinearWeight B D a b = (ArithmeticFunction.moebius a : ℝ) *
      leastFactorTerm (fun p => if B < p then leastOrderSign a p else 0) b := by
  rw [leastFactorTerm_eq_moebius]
  by_cases hb : 1 < b
  · by_cases hBb : B < b.minFac
    · have hmin : b.minFac ≤ b := Nat.minFac_le (by omega)
      have hprod : D < a * b := hD.trans_le (Nat.mul_le_mul_left a (by omega))
      simp only [roughBilinearWeight, ha, hb, hBa, hBb, hprod, and_self, if_true,
        bilinearSign, leastOrderSign]
      ring
    · simp [roughBilinearWeight, ha, hb, hBa, hBb]
  · simp [roughBilinearWeight, hb]

lemma roughBilinearWeight_bad_row (B D a b : ℕ) (h : ¬(1 < a ∧ B < a.minFac)) :
    roughBilinearWeight B D a b = 0 := by
  unfold roughBilinearWeight
  split_ifs with h'
  · exact False.elim (h ⟨h'.1, h'.2.2.2.1⟩)
  · rfl

/-- Although a row may contain many divisors, its complete signed sum is just
a single largest-prime-factor term. -/
theorem roughBilinearWeight_row_sum (B D a m : ℕ) (hm : 1 < m)
    (hD : D < a * (B + 1)) :
    (∑ b ∈ m.divisors, roughBilinearWeight B D a b) =
      if 1 < a ∧ B < a.minFac then
        -(ArithmeticFunction.moebius a : ℝ) *
          (if B < Nat.maxPrimeFac m then leastOrderSign a (Nat.maxPrimeFac m) else 0)
      else 0 := by
  by_cases ha : 1 < a ∧ B < a.minFac
  · simp_rw [roughBilinearWeight_large_row B D a _ ha.1 ha.2 hD]
    rw [← Finset.mul_sum, alladi_divisors m hm, if_pos ha]
    ring
  · simp only [roughBilinearWeight_bad_row B D a _ ha, Finset.sum_const_zero, if_neg ha]

/-- A full row has norm at most one, uniformly in the number of divisors. -/
theorem roughBilinearWeight_row_norm_le (B D a m : ℕ) (hD : D < a * (B + 1)) :
    ‖∑ b ∈ m.divisors, roughBilinearWeight B D a b‖ ≤ 1 := by
  by_cases hm : 1 < m
  · rw [roughBilinearWeight_row_sum B D a m hm hD]
    split_ifs with ha hB
    · rw [norm_mul, norm_neg]
      have hμ : ‖(ArithmeticFunction.moebius a : ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
      calc
        _ ≤ 1 * 1 := mul_le_mul hμ (leastOrderSign_norm_le _ _) (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    · simp
    · simp
  · have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl <;> simp [roughBilinearWeight]

/-- The corresponding column estimate follows from antisymmetry. -/
theorem roughBilinearWeight_column_norm_le (B D b m : ℕ) (hD : D < b * (B + 1)) :
    ‖∑ a ∈ m.divisors, roughBilinearWeight B D a b‖ ≤ 1 := by
  have he : (∑ a ∈ m.divisors, roughBilinearWeight B D a b) =
      -(∑ a ∈ m.divisors, roughBilinearWeight B D b a) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => roughBilinearWeight_swap B D b a
  rw [he, norm_neg]
  exact roughBilinearWeight_row_norm_le B D b m hD

lemma large_rough_rows_norm_le (B D n m : ℕ) :
    ‖∑ a ∈ n.divisors with D < a * (B + 1),
      ∑ b ∈ m.divisors, roughBilinearWeight B D a b‖ ≤
      ((n.divisors.filter fun a => D < a * (B + 1) ∧ 1 < a ∧ B < a.minFac).card : ℝ) := by
  calc
    _ ≤ ∑ a ∈ n.divisors with D < a * (B + 1),
        ‖∑ b ∈ m.divisors, roughBilinearWeight B D a b‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ n.divisors with D < a * (B + 1),
        if 1 < a ∧ B < a.minFac then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : 1 < a ∧ B < a.minFac
      · rw [if_pos h]
        exact roughBilinearWeight_row_norm_le B D a m (Finset.mem_filter.mp ha).2
      · simp only [if_neg h, roughBilinearWeight_bad_row B D a _ h, Finset.sum_const_zero, norm_zero,
          le_refl]
    _ = _ := by simp [Finset.filter_filter]

#print axioms roughBilinearWeight_row_sum
#print axioms roughBilinearWeight_row_norm_le
#print axioms large_rough_rows_norm_le
end Erdos371
