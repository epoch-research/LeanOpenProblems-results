import FormalConjectures.Util.ProblemImports
open Nat Polynomial
noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k
#check Polynomial.ext
#check Polynomial.map_mul
#check Polynomial.coeff_map
#check ZMod.intCast_zmod_eq_zero_iff_dvd
#check Int.emod_two_eq_zero_or_one
#check Int.even_iff
#check Polynomial.ext_iff
#check Polynomial.coeff_one
#check Polynomial.coeff_C
