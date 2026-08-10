import FormalConjectures.Util.ProblemImports

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  if n = 1 then C 1 + C 2 * X else X

theorem irreducible_one_add_two_X : Irreducible (C 1 + C 2 * X : ℚ[X]) := by
  apply irreducible_of_degree_eq_one
  rw [add_comm]
  have h_deg : 0 < (C 2 * X : ℚ[X]).degree := by
    rw [degree_C_mul_X (by decide)]
    decide
  rw [degree_add_C h_deg]
  rw [degree_C_mul_X (by decide)]

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  by_cases h : n = 1
  · subst h
    dsimp [apery_poly]
    exact irreducible_one_add_two_X
  · dsimp [apery_poly]
    rw [if_neg h]
    exact Polynomial.irreducible_X
