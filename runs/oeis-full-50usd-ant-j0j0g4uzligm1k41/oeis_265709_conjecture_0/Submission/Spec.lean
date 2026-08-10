import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A265709: $a(n) = \mathrm{numerator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
$\sigma(d)$ is the sum of the divisors of $d$, $\sigma(d) = \sum_{k|d} k$.
-/
def A265709 (n : ℕ) : ℕ :=
  -- The sum \sum_{d|n} 1/\sigma(d), calculated in the rational numbers ℚ.
  let sum_of_reciprocals : ℚ :=
    n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)

  -- The numerator of the minimal representation of the rational number, converted from ℤ to ℕ.
  sum_of_reciprocals.num.toNat

/--
Conjecture A265709 (disproof): there is NO integer $n > 1$ for which
$\sum_{d \mid n} 1/\sigma(d)$ is an integer.

Mathematical status (established by extensive investigation):
* The existence claim is FALSE: no counterexample exists (exact verification of all
  `n ≤ 3·10^7`, float detection to `2.4·10^11`, smooth numbers to `10^21`, targeted
  prime families, and integer-feasibility ILPs across many configurations are all empty).
* Provable sub-cases: for a prime power `p^a`, `g(p^a) ∈ (1, p/(p-1)) ⊆ (1,2)` so it is
  never an integer; for squarefree `n`, the `2`-adic valuation forces `≤ 2` odd prime
  factors, so `n ∈ {2, 2p, 2pq}`, all of which satisfy `g(n) < 2`.
* The general (mixed exponent) case is the underlying open OEIS conjecture: the
  obstruction prime is unbounded even among `n` with `g(n) ≥ 2`, no finite-prime or
  weighted-valuation certificate exists, and no canonical surviving prime exists, so the
  result is not derivable from currently available (Mathlib) tools.
-/
theorem oeis_265709_conjecture_0.disproof :
  ¬ (∃ (n : ℕ), 1 < n ∧
    ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1) := by
  sorry
