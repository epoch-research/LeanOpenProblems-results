import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  classical
  first
  | exact Polynomial.irreducible_of_degree_eq_one (R:=ℚ) (p:=apery_poly n) (by simp [apery_poly])
  | aesop (add simp [apery_poly])
  | grind [apery_poly]
  | simp_all [Irreducible, apery_poly]
