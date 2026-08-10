import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_1_eq : apery_poly 1 = C 1 + C 2 * X := by
  dsimp [apery_poly]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp

theorem degree_apery_poly_1 : (apery_poly 1).degree = 1 := by
  rw [apery_poly_1_eq]
  rw [add_comm]
  have h_deg : 0 < (C 2 * X : ℚ[X]).degree := by
    rw [degree_C_mul_X (by decide)]
    decide
  rw [degree_add_C h_deg]
  rw [degree_C_mul_X (by decide)]

theorem apery_poly_1_irreducible : Irreducible (apery_poly 1) := by
  apply irreducible_of_degree_eq_one
  exact degree_apery_poly_1

