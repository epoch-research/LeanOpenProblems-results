import FormalConjectures.Util.ProblemImports

open Polynomial

lemma irreducible_two_X_add_one : Irreducible (2 * X + 1 : ℚ[X]) := by
  apply irreducible_of_degree_eq_one
  compute_degree!
