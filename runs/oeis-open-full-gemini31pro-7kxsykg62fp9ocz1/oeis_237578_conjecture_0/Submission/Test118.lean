import Mathlib

theorem disproof : ¬ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by
  intro h
  have h38 := h 38 (by norm_num)
  rcases h38 with ⟨k, hk1, hk2, hk3⟩
  have : k ≤ 21 := by
    by_contra! h2
    have hk : (22 : ℝ) ≤ k := by exact_mod_cast h2
    have h3 : (19 : ℝ) ≤ k - 3 := by
      calc (19 : ℝ) = 22 - 3 := by norm_num
        _ ≤ k - 3 := sub_le_sub_right hk 3
    have h4 : (361 : ℝ) ≤ (k - 3)^2 := by
      calc (361 : ℝ) = 19 * 19 := by norm_num
        _ ≤ (k - 3) * (k - 3) := mul_self_le_mul_self (by norm_num) h3
        _ = (k - 3)^2 := by ring
    have h5 : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by
      calc (k - 3 : ℝ) = (k : ℝ) - 3 := rfl
        _ < 3 * Real.sqrt 38 + 3 - 3 := sub_lt_sub_right hk2 3
        _ = 3 * Real.sqrt 38 := by ring
    have hr : (0 : ℝ) < 3 * Real.sqrt 38 := by
      have : (0 : ℝ) < Real.sqrt 38 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h6 : (k - 3 : ℝ)^2 < 342 := by
      calc (k - 3 : ℝ)^2 = (k - 3) * (k - 3) := by ring
        _ ≤ (k - 3) * (3 * Real.sqrt 38) := by
          apply mul_le_mul_of_nonneg_left (le_of_lt h5)
          linarith
        _ < (3 * Real.sqrt 38) * (3 * Real.sqrt 38) := by
          apply mul_lt_mul_of_pos_right h5 hr
        _ = 9 * (Real.sqrt 38 * Real.sqrt 38) := by ring
        _ = 9 * 38 := by
          have : Real.sqrt 38 * Real.sqrt 38 = 38 := by
            exact Real.mul_self_sqrt (by norm_num)
          rw [this]
        _ = 342 := by norm_num
    linarith
  sorry
