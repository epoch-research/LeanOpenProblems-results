import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

-- placeholder scratch: inspect API for v2 central binomial
#check Nat.two_dvd_centralBinom_of_one_le
#check padicValNat_choose
#check Nat.factorization_choose
#check Nat.centralBinom_eq_two_mul_choose
#check Nat.choose_pos
#check Polynomial.irreducible_iff_lt_natDegree_lt
#check Polynomial.map_dvd_map
#check Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
