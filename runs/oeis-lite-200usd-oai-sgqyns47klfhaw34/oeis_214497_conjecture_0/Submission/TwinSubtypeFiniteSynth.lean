import FormalConjectures.Util.ProblemImports

#synth Finite {m : ℕ // Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)}
#synth Infinite {m : ℕ // Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)}

example : False := by
  exact not_finite {m : ℕ // Nat.Prime (m - 1) ∧ Nat.Prime (m + 1)}
