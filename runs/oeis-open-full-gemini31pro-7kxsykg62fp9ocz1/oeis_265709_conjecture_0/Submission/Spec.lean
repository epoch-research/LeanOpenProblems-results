import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

theorem oeis_265709_conjecture_0 :
  ∃ (n : ℕ), 1 < n ∧
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1 := by
  sorry

theorem oeis_265709_conjecture_0.disproof : ¬ (type_of% @oeis_265709_conjecture_0) := by
  sorry
