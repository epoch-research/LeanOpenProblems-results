import FormalConjectures.Util.ProblemImports

open Nat

/--
Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

open Polynomial

/--
The polynomial associated with the $n$-th Apéry number:
$$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$$
-/
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

/--
Conjecture: For each n=1,2,3,... the polynomial a_n(x) = Sum_{k=0..n} C(n,k)^2*C(n+k,k)*x^k is irreducible over the field of rational numbers. - _Zhi-Wei Sun_, Mar 21 2013
-/
theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  sorry

theorem apery_poly_irreducible.disproof : ¬ (type_of% @apery_poly_irreducible) := sorry
