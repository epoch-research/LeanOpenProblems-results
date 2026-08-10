import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  apply Polynomial.irreducible_of_degree_eq_one
  simp [apery_poly]
