import Mathlib

theorem disproof : ¬ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by
  intro h
  have h38 := h 38 (by norm_num)
  rcases h38 with ⟨k, hk1, hk2, hk3⟩
  have : k ≤ 21 := by
    by_contra! h2
    have hk : (22 : ℝ) ≤ k := by exact_mod_cast h2
    have h3 : (19 : ℝ) ≤ k - 3 := by linarith [hk]
    have h4 : (361 : ℝ) ≤ (k - 3)^2 := by
      calc (361 : ℝ) = 19 * 19 := by norm_num
        _ ≤ (k - 3) * (k - 3) := mul_self_le_mul_self (by norm_num) h3
        _ = (k - 3)^2 := by ring
    have h5 : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by linarith [hk2]
    have hr : (0 : ℝ) ≤ 3 * Real.sqrt 38 := by positivity
    have h6 : (k - 3 : ℝ)^2 < (3 * Real.sqrt 38)^2 := by
      calc (k - 3 : ℝ)^2 = (k - 3) * (k - 3) := by ring
        _ < (3 * Real.sqrt 38) * (3 * Real.sqrt 38) := by
          nlinarith [h5, show (0 : ℝ) ≤ k - 3 by linarith [hk]]
        _ = (3 * Real.sqrt 38)^2 := by ring
    have h7 : (3 * Real.sqrt 38 : ℝ)^2 = 342 := by
      calc (3 * Real.sqrt 38 : ℝ)^2 = 3^2 * (Real.sqrt 38)^2 := mul_pow 3 (Real.sqrt 38) 2
        _ = 9 * 38 := by
          rw [Real.sq_sqrt (by norm_num)]
          norm_num
        _ = 342 := by norm_num
    linarith [h4, h6, h7]
  sorry
