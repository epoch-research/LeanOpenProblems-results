import FormalConjectures.Util.ProblemImports

example (n : ℕ) : Finite {p // Nat.Prime p ∧ p ≤ n} := by
  infer_instance
