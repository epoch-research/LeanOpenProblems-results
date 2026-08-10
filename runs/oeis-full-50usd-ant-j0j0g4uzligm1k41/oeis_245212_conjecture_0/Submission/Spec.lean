import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A245212: $a(n) = n \cdot \tau(n) - \sum_{d|n, d<n} d \cdot \tau(d)$,
where $\tau(n)$ is the number of divisors of $n$.
The formula uses the set of proper divisors for the sum.
The result is an integer ($\mathbb{Z}$) to account for negative values.
-/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * (n.divisors.card : ℤ) - n.properDivisors.sum
    (fun d => (d : ℤ) * (d.divisors.card : ℤ))

-- The sum of divisors function $\sigma_1(n)$, cast to ℤ.
def sigma (n : ℕ) : ℤ :=
  n.divisors.sum (fun d => (d : ℤ))

/--
%C A245212 Conjecture: a(n) = sigma(n) iff n is a power of 2 (A000079).
-/
theorem oeis_245212_conjecture_0 (n : ℕ) (h : n > 0) :
    a n = sigma n ↔ n.isPowerOfTwo := by
  sorry
