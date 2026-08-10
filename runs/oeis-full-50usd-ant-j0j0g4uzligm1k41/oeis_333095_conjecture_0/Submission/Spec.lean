import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A333095: the $n$-th order Taylor polynomial (centered at 0) of $c(x)^{3n}$ evaluated at $x = 1$.
The sequence is defined by the sum of coefficients of the Taylor polynomial:
$$a(n) = \sum_{k = 0}^n \frac{3n}{3n+2k}\binom{3n+2k}{k} \quad \text{for } n \ge 1, \text{ and } a(0) = 1.$$
The result of the $\mathbb{Q}$ sum is known to be an integer, which justifies the floor/toNat conversion.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    ((Finset.sum (range (n + 1)) fun k =>
      let N := 3 * n
      let term_val : ℚ := (N : ℚ) / (N + 2 * k : ℚ) * ((N + 2 * k).choose k : ℚ)
      term_val
    ).floor).toNat

/--
We conjecture that the sequence satisfies the stronger supercongruences
$a(n p^k) \equiv a(n p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333095_conjecture_0 (p n k : ℕ) :
  p.Prime → 5 ≤ p → 0 < n → 0 < k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  sorry
