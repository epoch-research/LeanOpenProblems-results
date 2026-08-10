import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_3_eq : apery_poly 3 = 1 + C 36 * X + C 90 * X ^ 2 + C 20 * X ^ 3 := by
  unfold apery_poly
  simp [Finset.sum_range_succ, choose, C_eq_algebraMap]
  norm_num
