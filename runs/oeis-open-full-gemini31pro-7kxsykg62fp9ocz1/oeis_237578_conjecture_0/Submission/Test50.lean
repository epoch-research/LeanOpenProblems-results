import Mathlib

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

theorem check_part1_false : ¬ (∀ n : ℕ, 2 < n → a n > 0) := by sorry
