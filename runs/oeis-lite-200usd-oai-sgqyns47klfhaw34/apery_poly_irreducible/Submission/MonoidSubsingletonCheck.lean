import FormalConjectures.Util.ProblemImports
open Polynomial
#synth Subsingleton (Monoid ℚ[X])
example (M1 M2 : Monoid ℚ[X]) : M1 = M2 := by
  exact Subsingleton.elim _ _
