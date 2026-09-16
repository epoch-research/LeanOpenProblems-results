import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence A218656: Number of ways to write $2n+1$ as $x+y$ with $0 < x < y$ and $x^4 + y^4$ prime.
This is equivalent to the number of $k \in \{1, \dots, n\}$ such that $k^4 + (2n+1-k)^4$ is prime.
-/
def a (n : ℕ) : ℕ :=
  card ((Icc 1 n).filter fun k : ℕ => Nat.Prime (k ^ 4 + (2 * n + 1 - k) ^ 4))

/--
Auxiliary theorem formalizing the empirical claim about the verification range
for the $x^4 + y^4$ case.
The claim: "no exceptions for x^4 + y^4" for $2n+1 \le 10^6$.
This is equivalent to $a(n) > 0$ for $1 \le n \le (10^6-1)/2 = 499999$.
Note: $500000 = 10^6/2$. If $2n+1 \le 10^6$, then $2n \le 999999$, so $n \le 499999$.
-/
theorem oeis_A218656_verified_range (n : ℕ) (hval : n ≤ 499999) (hn : 0 < n) : a n > 0 := sorry

theorem oeis_A218656_verified_range.disproof : ¬ (type_of% @oeis_A218656_verified_range) := sorry
