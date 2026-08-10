import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial
open Google

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) :=
  answer(sorry)

#print apery_poly_irreducible
#print axioms apery_poly_irreducible



