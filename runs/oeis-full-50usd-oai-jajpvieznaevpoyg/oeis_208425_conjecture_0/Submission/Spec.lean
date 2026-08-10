import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A208425: Expansion of $\sum_{n\ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$.
The $n$-th term $a(n)$ is given by the known combinatorial identity:
$$ a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n-k}{k} \binom{n+k}{k} $$
-/
def a (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) * ((n - k).choose k) * ((n + k).choose k)


/-- Conjecture: (i) For any prime p > 3 and positive integer n,
the number (a(p*n)-a(n))/(p*n)^3 is always a p-adic integer. -/
theorem oeis_208425_conjecture_0 (p : ℕ) (hp : p.Prime) (hpgt3 : p > 3) (n : ℕ) (hn : n > 0) :
  padicValRat p (((a (p * n) : ℚ) - (a n : ℚ)) / ((p * n : ℚ) ^ 3)) ≥ 0 :=
by sorry
