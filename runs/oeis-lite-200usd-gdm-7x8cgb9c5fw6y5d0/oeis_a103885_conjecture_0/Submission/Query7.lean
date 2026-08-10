import FormalConjectures.Util.ProblemImports

#check (12 : ℝ[X])
example (N : ℕ) : (12 : ℝ[X]).coeff N = if N = 0 then 12 else 0 := by
  sorry
