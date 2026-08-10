import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_2_coeff : (apery_poly 2).coeff 1 = 12 := by
  unfold apery_poly
  norm_num
