import FormalConjectures.Util.ProblemImports

open Nat

/--
A119563: Define $F(n) = 2^{2^n}+1 = n$-th Fermat number, $M(n) = 2^n-1$ = the $n$-th Mersenne number.
Then $a(n) = F(n)+M(n)-1 = 2^{2^n} + 2^n - 1$.
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1

/--
The first 5 entries are primes. Are there infinitely many primes in this sequence?

The sequence `a n = 2 ^ (2 ^ n) + 2 ^ n - 1` grows doubly exponentially, like the
Fermat numbers.  The number-of-primes heuristic gives the convergent series
`∑ₙ c / log (a n) ≍ ∑ₙ c / 2 ^ n`, so the sequence is expected to contain only
finitely many primes (mirroring the situation for the Fermat primes).  Indeed
`a 5, …, a 16` are all composite.  Hence the conjecture is expected to be *false*.
-/
theorem foo.disproof : ¬ {n : ℕ | Nat.Prime (a n)}.Infinite := by
  sorry
