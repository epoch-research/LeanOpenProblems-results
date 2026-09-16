import Mathlib

theorem disproof : ¬ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by
  intro h
  have h38 := h 38 (by norm_num)
  rcases h38 with ⟨k, hk1, hk2, hk3⟩
  have hk_le : k ≤ 21 := by
    by_contra! hk_gt
    have h1 : (22 : ℝ) ≤ k := by exact_mod_cast hk_gt
    have h2 : (19 : ℝ) ≤ k - 3 := by
      calc (19 : ℝ) = 22 - 3 := by norm_num
        _ ≤ k - 3 := by exact sub_le_sub_right h1 3
    have h3 : (361 : ℝ) ≤ (k - 3)^2 := by
      calc (361 : ℝ) = 19 * 19 := by norm_num
        _ ≤ (k - 3) * (k - 3) := mul_self_le_mul_self (by norm_num) h2
        _ = (k - 3)^2 := by ring
    have h4 : (k - 3 : ℝ) < 3 * Real.sqrt 38 := by
      calc (k - 3 : ℝ) = (k : ℝ) - 3 := rfl
        _ < 3 * Real.sqrt (38 : ℝ) + 3 - 3 := by exact sub_lt_sub_right hk2 3
        _ = 3 * Real.sqrt 38 := by ring
    have h5 : (0 : ℝ) ≤ 3 * Real.sqrt 38 := by positivity
    have h6 : (k - 3 : ℝ)^2 < 342 := by
      calc (k - 3 : ℝ)^2 = (k - 3) * (k - 3) := by ring
        _ < (3 * Real.sqrt 38) * (3 * Real.sqrt 38) := by
          have h_pos : (0 : ℝ) < k - 3 := by
            calc (0 : ℝ) < 19 := by norm_num
              _ ≤ k - 3 := h2
          exact mul_lt_mul h4 (le_of_lt h4) h_pos h5
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
  · have : Nat.primeCounting (21 * 38) = 139 := rfl; rw [this]; sorry
