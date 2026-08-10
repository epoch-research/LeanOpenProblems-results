import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators


/--
A333096: The $n$-th order Taylor polynomial (centered at 0) of $c(x)^{4n}$ evaluated at $x=1$, where $c(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is the o.g.f. of the sequence of Catalan numbers $A000108$.
The sequence is defined by the formula:
$$a(n) = \sum_{k = 0}^n \frac{4n}{4n+k}\binom{4n+2k-1}{k} \quad \text{for } n \ge 1$$
and $a(0) = 1.$$
The summand is the $k$-th coefficient of the power series $c(x)^{4n}$, which is an integer.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      -- Since the combinatorial identity guarantees exact divisibility, Nat division is equivalent to integer division.
      numerator / denominator

/--
We conjecture that the sequence satisfies the stronger supercongruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{\left(3k\right)}}$ for prime $p \ge 5$ and positive integers $n$ and $k$.
-/


theorem oeis_333096_conjecture_0 (p k n : ℕ) :
  (p.Prime ∧ p ≥ 5 ∧ n > 0 ∧ k > 0) →
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  sorry
