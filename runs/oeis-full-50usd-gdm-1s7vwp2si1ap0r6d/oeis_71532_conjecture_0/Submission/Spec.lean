import FormalConjectures.Util.ProblemImports

open BigOperators Int Real


set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

lemma a_2 : a 2 = 0 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  decide

lemma a_2_le_sqrt : (a 2 : ℝ) ≤ sqrt (2 : ℝ) := by
  have h1 : a 2 = 0 := a_2
  rw [h1]
  norm_cast
  exact sqrt_nonneg (2 : ℝ)


lemma a_4 : a 4 = 2 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  decide


lemma a_4_le_sqrt : (a 4 : ℝ) ≤ sqrt (4 : ℝ) := by
  have h1 : a 4 = 2 := a_4
  rw [h1]
  norm_cast
  norm_num


lemma a_121 : a 121 = 11 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_121_le_sqrt : (a 121 : ℝ) ≤ sqrt (121 : ℝ) := by
  have h1 : a 121 = 11 := a_121
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_123 : a 123 = 11 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_123_le_sqrt : (a 123 : ℝ) ≤ sqrt (123 : ℝ) := by
  have h1 : a 123 = 11 := a_123
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_127 : a 127 = 11 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_127_le_sqrt : (a 127 : ℝ) ≤ sqrt (127 : ℝ) := by
  have h1 : a 127 = 11 := a_127
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_146 : a 146 = 12 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_146_le_sqrt : (a 146 : ℝ) ≤ sqrt (146 : ℝ) := by
  have h1 : a 146 = 12 := a_146
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num


lemma a_204 : a 204 = 14 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_204_le_sqrt : (a 204 : ℝ) ≤ sqrt (204 : ℝ) := by
  have h1 : a 204 = 14 := a_204
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num


lemma a_205 : a 205 = 13 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_205_le_sqrt : (a 205 : ℝ) ≤ sqrt (205 : ℝ) := by
  have h1 : a 205 = 13 := a_205
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_206 : a 206 = 14 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_206_le_sqrt : (a 206 : ℝ) ≤ sqrt (206 : ℝ) := by
  have h1 : a 206 = 14 := a_206
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_208 : a 208 = 14 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_208_le_sqrt : (a 208 : ℝ) ≤ sqrt (208 : ℝ) := by
  have h1 : a 208 = 14 := a_208
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_256 : a 256 = 16 := by
  unfold a
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  simp only [Int.toNat]
  simp only [neg_one_pow_eq_ite]
  norm_num

lemma a_256_le_sqrt : (a 256 : ℝ) ≤ sqrt (256 : ℝ) := by
  have h1 : a 256 = 16 := a_256
  rw [h1]
  norm_cast
  apply Real.le_sqrt_of_sq_le
  norm_num

theorem oeis_71532_conjecture_0.disproof : ¬ (∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) := by
  rintro ⟨N, hN⟩
  have h_gt : N > 256 := by
    by_contra! h
    rcases lt_or_ge N 3 with hN_lt | hN_ge
    · have := hN 2 (by omega)
      exact not_lt.mpr a_2_le_sqrt this
    · rcases lt_or_ge N 5 with hN_lt | hN_ge
      · have := hN 4 (by omega)
        exact not_lt.mpr a_4_le_sqrt this
      · rcases lt_or_ge N 122 with hN_lt | hN_ge
        · have := hN 121 (by omega)
          exact not_lt.mpr a_121_le_sqrt this
        · rcases lt_or_ge N 124 with hN_lt | hN_ge
          · have := hN 123 (by omega)
            exact not_lt.mpr a_123_le_sqrt this
          · rcases lt_or_ge N 128 with hN_lt | hN_ge
            · have := hN 127 (by omega)
              exact not_lt.mpr a_127_le_sqrt this
            · rcases lt_or_ge N 147 with hN_lt | hN_ge
              · have := hN 146 (by omega)
                exact not_lt.mpr a_146_le_sqrt this
              · rcases lt_or_ge N 205 with hN_lt | hN_ge
                · have := hN 204 (by omega)
                  exact not_lt.mpr a_204_le_sqrt this
                · rcases lt_or_ge N 206 with hN_lt | hN_ge
                  · have := hN 205 (by omega)
                    exact not_lt.mpr a_205_le_sqrt this
                  · rcases lt_or_ge N 207 with hN_lt | hN_ge
                    · have := hN 206 (by omega)
                      exact not_lt.mpr a_206_le_sqrt this
                    · rcases lt_or_ge N 209 with hN_lt | hN_ge
                      · have := hN 208 (by omega)
                        exact not_lt.mpr a_208_le_sqrt this
                      · have := hN 256 (by omega)
                        exact not_lt.mpr a_256_le_sqrt this
  sorry
