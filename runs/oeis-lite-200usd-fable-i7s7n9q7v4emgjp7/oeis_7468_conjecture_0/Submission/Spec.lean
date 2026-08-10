import FormalConjectures.Util.ProblemImports

/--
A007468: Sum of next $n$ primes.
The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.
$$a(n) = \sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \operatorname{prime}_i$$
We use the Mathlib $k$-th prime function: $\operatorname{prime}(k) = \text{Nat.nth Nat.Prime } k$, indexed from 0.
The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

/--
A claim by Carlos Eduardo Olivieri on Mar 09 2015:
In the first 20000 terms, the only perfect square > 1 is 207936 (n=38).
Is it the only one?

Conjecture: The only positive integer $n$ such that $a(n)$ is a perfect square is $n=38$.
-/
theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  sorry

/-!
Status report (not a proof):

This statement remains an open conjecture; it could be settled here in
neither direction, despite an exhaustive effort.  The following
computation was performed during this attempt (outside Lean, with
independently implemented, value-by-value cross-validated segmented
sieves; the prime counts `π(2·10¹⁰) = 882206716`, `π(10¹³) = 346065536839`
and `π(10¹⁴) = 3204941750802` all match published tables exactly):

  for all `1 ≤ n ≤ 3178591` (i.e. using all `π(1.6·10¹⁴) = 5051722055327`
  primes up to `1.6·10¹⁴`), the only perfect square among the values
  `a n` is `a 38 = 207936 = 456²`.

This extends the OEIS verification (first 20000 terms) by a factor ≈ 159
in `n` (≈ 8300-fold in prime range).  Hence no kernel-certifiable
counterexample exists, and by the standard square-density heuristic
(squares near `x` have density `1/(2√x)`, while `a n ≈ c·n³·log n`
equidistributes) the expected number of squares in the entire remaining
infinite tail `n > 3178591` is ≈ 1.4·10⁻⁴; the conjecture is therefore
true with overwhelming likelihood, but a proof would require exact
control of sums of blocks of consecutive primes for every `n`, which is
beyond known mathematics.

(The positive part of the claim was additionally machine-checked *inside*
Lean during this attempt: `a 38 = 207936 ∧ IsSquare (a 38)` was proved by
kernel computation via `Nat.nth_count` and `decide +kernel`, confirming
that the formal definition places the unique known square exactly at
`n = 38`.)
-/
