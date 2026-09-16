import Mathlib

lemma factorial_gt (N : ℕ) (h : N ≥ 30) : (2 * N + 2).factorial > 4 * N := by
  have h1 : 2 * N + 2 = (2 * N + 1) + 1 := by omega
  rw [h1, Nat.factorial_succ]
  have h2 : (2 * N + 1).factorial ≥ 2 := by
    have h3 : 2 * N + 1 = 2 * N + 1 := rfl
    -- just apply induction or self_le_factorial?
    sorry
  sorry
