import FormalConjectures.Util.ProblemImports

open Polynomial

example (N : ℕ) : (12 : Polynomial ℝ).coeff N = if N = 0 then 12 else 0 := by
  simp
