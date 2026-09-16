import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

theorem oeis_a010846_granville_conjecture :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n :=
by sorry

theorem disproof : ¬ (type_of% @oeis_a010846_granville_conjecture) := by
  intro h
  sorry
