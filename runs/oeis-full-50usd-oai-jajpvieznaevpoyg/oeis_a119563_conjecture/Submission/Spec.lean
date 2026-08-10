import FormalConjectures.Util.ProblemImports

open Nat

/--
A119563: Define $F(n) = 2^{2^n}+1 = n$-th Fermat number, $M(n) = 2^n-1$ = the $n$-th Mersenne number.
Then $a(n) = F(n)+M(n)-1 = 2^{2^n} + 2^n - 1$.
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1

/--
The first 5 entries are primes. Are there infinitely many primes in this sequence?
-/
theorem oeis_a119563_conjecture : {n : ℕ | Nat.Prime (a n)}.Infinite := by sorry
