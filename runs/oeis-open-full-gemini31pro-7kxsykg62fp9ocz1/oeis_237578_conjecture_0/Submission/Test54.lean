import Mathlib

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

theorem disproof : ¬ (∀ n : ℕ, 2 < n → a n > 0) ∨
                   ¬ (∀ n : ℕ, a n = 1 ↔ n = 5 ∨ n = 8 ∨ n = 13) ∨
                   ¬ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by
  sorry
