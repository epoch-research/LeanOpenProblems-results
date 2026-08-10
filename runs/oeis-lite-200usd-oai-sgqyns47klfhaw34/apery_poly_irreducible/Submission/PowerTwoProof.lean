import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

-- Just inspect APIs for reverse coefficient and Eisenstein over Z.
#check reverse
#check coeff_reverse
#check Polynomial.IsEisensteinAt.irreducible
#check Ideal.span_singleton_prime
#check Int.prime_two
#check Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
#check Polynomial.map_reverse
#check Polynomial.Monic.reverse
#check Polynomial.reverse_monic
#check Polynomial.natDegree_reverse
#check Polynomial.leadingCoeff_reverse
#check Polynomial.IsPrimitive
#check Polynomial.IsPrimitive.of_C_primitive
#check Polynomial.isPrimitive_iff_isPrimitive_map_of_injective
