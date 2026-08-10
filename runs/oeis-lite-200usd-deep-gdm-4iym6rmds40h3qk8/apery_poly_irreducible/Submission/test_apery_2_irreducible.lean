import FormalConjectures.Util.ProblemImports

open Polynomial

noncomputable def p : ℚ[X] := C 1 + C 12 * X + C 6 * X^2

example : p.natDegree = 2 := by
  unfold p
  compute_degree!
