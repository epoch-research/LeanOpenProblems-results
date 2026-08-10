import FormalConjectures.Util.ProblemImports

example : ({m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)} : Set ℕ).Finite := by
  exact?

example : ¬ ({m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)} : Set ℕ).Infinite := by
  exact?

example : ({m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)} : Set ℕ).Infinite := by
  exact?
