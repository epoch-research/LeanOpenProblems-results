import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

-- integer version
noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

#check Polynomial.reverse
#check Polynomial.reflect
#check Polynomial.irreducible_of_eisenstein_criterion
#check Ideal.span_singleton_prime
#check Int.prime_two
#check Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
#check Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
#check Polynomial.Monic.irreducible_of_irreducible_map
#check Polynomial.reverse_mul_of_domain
#check Polynomial.reverse_eq_zero
#check Polynomial.coeff_reverse
