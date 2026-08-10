import FormalConjectures.Util.ProblemImports
open Nat Polynomial
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

example : apery_poly 2 = (6 : ℚ[X]) * X^2 + 12 * X + 1 := by
  norm_num [apery_poly]
  ring

example : ¬ Irreducible (apery_poly 2) := by
  norm_num [apery_poly, Irreducible]
