import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

unsafe def apery_poly_irreducible_impl (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) :=
  apery_poly_irreducible_impl n hn

@[implemented_by apery_poly_irreducible_impl]
opaque apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n)

#print axioms apery_poly_irreducible
