import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A275768: $a(n)$ is the number of ways to express $n = \frac{\operatorname{prime}(i) + \operatorname{prime}(j)}{2}$ when $\frac{|\operatorname{prime}(i) - \operatorname{prime}(j)|}{2}$ also is prime.
This is equivalent to counting the number of primes $q$ such that $n - q$ and $n + q$ are also prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

/-- OEIS A275768 conjecture 0: Does a(n) = 4 occur for any n? -/
theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  sorry

theorem oeis_275768_conjecture_0.disproof : ¬ (type_of% @oeis_275768_conjecture_0) := sorry
