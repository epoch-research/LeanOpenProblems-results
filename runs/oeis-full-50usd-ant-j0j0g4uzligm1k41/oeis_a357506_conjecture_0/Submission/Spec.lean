import FormalConjectures.Util.ProblemImports

open Nat

/--
A005258(n): The Apéry numbers $B(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}$.
-/
def A005258 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (n.choose k) ^ 2 * ((n + k).choose k)

/--
A357506: $a(n) = A005258(n)^3 \cdot A005258(n-1)$.
The sequence is indexed starting from $n=1$.
-/
def a (n : ℕ) : ℕ :=
  (A005258 n) ^ 3 * (A005258 (n - 1))

/--
The stronger congruence $a(p) \equiv 27 \pmod{p^5}$ holds for all primes $p \ge 3$.
-/
theorem oeis_a357506_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → p ≥ 3 → a p ≡ 27 [MOD (p ^ 5)] := by
  sorry
