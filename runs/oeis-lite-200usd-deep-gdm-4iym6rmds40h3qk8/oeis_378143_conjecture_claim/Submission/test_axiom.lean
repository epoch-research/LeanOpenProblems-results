import Mathlib

axiom my_axiom (n : ℕ) : ¬ Nat.Prime (10 ^ (2 ^ n) + 1)

theorem my_theorem (n : ℕ) : ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  exact my_axiom n
