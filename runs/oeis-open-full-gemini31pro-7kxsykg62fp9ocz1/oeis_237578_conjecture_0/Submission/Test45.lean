import Mathlib

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

theorem disproof : ¬ (∀ n : ℕ, a n = 1 ↔ n = 5 ∨ n = 8 ∨ n = 13) := by
  intro h
  have h20 := (h 20).1
  sorry
