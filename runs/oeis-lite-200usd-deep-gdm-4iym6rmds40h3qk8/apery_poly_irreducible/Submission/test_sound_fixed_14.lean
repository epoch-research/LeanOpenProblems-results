import FormalConjectures.Util.ProblemImports

open Polynomial

theorem irreducible_one_add_two_X : Irreducible (C 1 + C 2 * X : ℚ[X]) := by
  apply irreducible_of_degree_eq_one
  rw [add_comm]
  have h_deg : 0 < (C 2 * X : ℚ[X]).degree := by
    rw [degree_C_mul_X (by decide)]
    decide
  rw [degree_add_C h_deg]
  rw [degree_C_mul_X (by decide)]
