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
Conjecture A265709: Are there numbers $n > 1$ such that $\sum_{d|n} 1/\sigma(d)$ is an integer?
-/
theorem oeis_265709_conjecture_0 :
  ∃ (n : ℕ), 1 < n ∧
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1 := by
  sorry

theorem oeis_265709_conjecture_0.disproof : ¬ (type_of% @oeis_265709_conjecture_0) := sorry
