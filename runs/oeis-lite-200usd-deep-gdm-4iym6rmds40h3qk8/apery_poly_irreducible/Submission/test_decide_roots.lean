import FormalConjectures.Util.ProblemImports

open Polynomial

noncomputable def p : ℚ[X] := C 1 + C 12 * X + C 6 * X^2

theorem p_no_roots : p.roots = 0 := by
  decide
