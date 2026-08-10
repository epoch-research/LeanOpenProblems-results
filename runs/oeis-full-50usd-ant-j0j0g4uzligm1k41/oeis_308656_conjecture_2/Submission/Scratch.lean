import FormalConjectures.Util.ProblemImports
open Nat Int BigOperators Finset

-- Test the reduction identity as a ring identity over ℤ.
example (t c d : ℤ) :
    48 * (t^2 + (4*c^2 + c) + (3*d^2 + d)/2) + 5
      = 48 * t^2 + 3*(8*c+1)^2 + 2*(6*d+1)^2 := by
  sorry
