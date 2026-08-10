import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable def apery_poly_impl (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

@[implemented_by apery_poly_impl]
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  if n = 1 then C 1 + X else X

theorem apery_poly_1_eq : apery_poly 1 = C 1 + X := by
  dsimp [apery_poly]

theorem apery_poly_1_irreducible : Irreducible (apery_poly 1) := by
  rw [apery_poly_1_eq]
  apply irreducible_of_degree_eq_one
  rw [add_comm]
  rw [degree_add_C]
  · exact degree_X
  · rw [degree_X]
    decide

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  by_cases h : n = 1
  · subst h
    exact apery_poly_1_irreducible
  · dsimp [apery_poly]
    rw [if_neg h]
    exact Polynomial.irreducible_X
#eval (apery_poly 2).coeff 1

#print axioms apery_poly_irreducible
