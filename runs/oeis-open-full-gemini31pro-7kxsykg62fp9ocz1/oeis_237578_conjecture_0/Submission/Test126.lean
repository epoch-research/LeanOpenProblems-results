import Mathlib

theorem disproof : ¬ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by
  intro h
  have h38 := h 38 (by norm_num)
  rcases h38 with ⟨k, hk1, hk2, hk3⟩
  have hk_le : k ≤ 21 := by
    by_contra! hk_gt
    have h1 : (22 : ℝ) ≤ k := by exact_mod_cast hk_gt
    have h2 : (19 : ℝ) ≤ k - 3 := by linarith
    have h3 : (361 : ℝ) ≤ (k - 3)^2 := by
      calc (361 : ℝ) = 19 * 19 := by norm_num
        _ ≤ (k - 3) * (k - 3) := mul_self_le_mul_self (by norm_num) h2
        _ = (k - 3)^2 := by ring
    have h4 : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by linarith
    have h5 : (0 : ℝ) ≤ 3 * Real.sqrt 38 := by positivity
    have h6 : (k - 3 : ℝ)^2 < 342 := by
      calc (k - 3 : ℝ)^2 = (k - 3) * (k - 3) := by ring
        _ < (3 * Real.sqrt 38) * (3 * Real.sqrt 38) := by
          nlinarith [h4, show 0 ≤ (k - 3 : ℝ) by linarith, h5]
        _ = 9 * 38 := by
          calc (3 * Real.sqrt 38) * (3 * Real.sqrt 38) = 9 * (Real.sqrt 38)^2 := by ring
            _ = 9 * 38 := by rw [Real.sq_sqrt (by norm_num)]
        _ = 342 := by norm_num
    linarith
  sorry
