import Mathlib

theorem oeis_237578_conjecture_0_proof : ¬ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by sorry
