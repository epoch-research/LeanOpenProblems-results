import FormalConjectures.Util.ProblemImports

example (s : Set ℕ) : s.Finite := by
  exact?

example (s : Set ℕ) : ¬ s.Infinite := by
  exact?

example : ({m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)} : Set ℕ).Finite := by
  apply Set.toFinite
