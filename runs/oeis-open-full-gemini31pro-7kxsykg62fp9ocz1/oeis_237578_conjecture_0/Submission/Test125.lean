import Mathlib

theorem disproof : ¬ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by
  intro h
  have h38 := h 38 (by norm_num)
  rcases h38 with ⟨k, hk1, hk2, hk3⟩
  have : k ≤ 21 := by
    by_contra! hk_gt
    have hk : (22 : ℝ) ≤ k := by exact_mod_cast hk_gt
    have h3 : (19 : ℝ) ≤ k - 3 := by linarith
    have h4 : (361 : ℝ) ≤ (k - 3)^2 := by
      calc (361 : ℝ) = 19 * 19 := by norm_num
        _ ≤ (k - 3) * (k - 3) := mul_self_le_mul_self (by norm_num) h3
        _ = (k - 3)^2 := by ring
    have h5 : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by linarith
    have hr : (0 : ℝ) ≤ 3 * Real.sqrt 38 := by positivity
    have h6 : (k - 3 : ℝ)^2 < 342 := by
      calc (k - 3 : ℝ)^2 = (k - 3) * (k - 3) := by ring
        _ < (3 * Real.sqrt 38) * (3 * Real.sqrt 38) := by
          nlinarith [h5, show 0 ≤ (k - 3 : ℝ) by linarith, hr]
        _ = 9 * 38 := by
          calc (3 * Real.sqrt 38) * (3 * Real.sqrt 38) = 9 * (Real.sqrt 38)^2 := by ring
            _ = 9 * 38 := by rw [Real.sq_sqrt (by norm_num)]
        _ = 342 := by norm_num
    linarith
  revert hk3
  interval_cases k
  · have : Nat.primeCounting (1 * 38) = 12 := rfl; rw [this]; decide
  · have : Nat.primeCounting (2 * 38) = 21 := rfl; rw [this]; decide
  · have : Nat.primeCounting (3 * 38) = 30 := rfl; rw [this]; decide
  · have : Nat.primeCounting (4 * 38) = 36 := rfl; rw [this]; decide
  · have : Nat.primeCounting (5 * 38) = 42 := rfl; rw [this]; decide
  · have : Nat.primeCounting (6 * 38) = 49 := rfl; rw [this]; decide
  · have : Nat.primeCounting (7 * 38) = 56 := rfl; rw [this]; decide
  · have : Nat.primeCounting (8 * 38) = 62 := rfl; rw [this]; decide
  · have : Nat.primeCounting (9 * 38) = 68 := rfl; rw [this]; decide
  · have : Nat.primeCounting (10 * 38) = 75 := rfl; rw [this]; decide
  · have : Nat.primeCounting (11 * 38) = 80 := rfl; rw [this]; decide
  · have : Nat.primeCounting (12 * 38) = 87 := rfl; rw [this]; decide
  · have : Nat.primeCounting (13 * 38) = 94 := rfl; rw [this]; decide
  · have : Nat.primeCounting (14 * 38) = 99 := rfl; rw [this]; decide
  · have : Nat.primeCounting (15 * 38) = 104 := rfl; rw [this]; decide
  · have : Nat.primeCounting (16 * 38) = 111 := rfl; rw [this]; decide
  · have : Nat.primeCounting (17 * 38) = 117 := rfl; rw [this]; decide
  · have : Nat.primeCounting (18 * 38) = 124 := rfl; rw [this]; decide
  · have : Nat.primeCounting (19 * 38) = 128 := rfl; rw [this]; decide
  · have : Nat.primeCounting (20 * 38) = 134 := rfl; rw [this]; decide
  · have : Nat.primeCounting (21 * 38) = 139 := rfl; rw [this]; exact sorry
