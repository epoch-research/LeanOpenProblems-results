import FormalConjectures.Util.ProblemImports

open Nat

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_irreducible_1 : Irreducible (apery_poly 1) := by
  have h1 : apery_poly 1 = 2 * X + 1 := by
    dsimp [apery_poly]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp [C_ofNat]
    ring
  rw [h1]
  apply irreducible_of_degree_eq_one
  compute_degree!
