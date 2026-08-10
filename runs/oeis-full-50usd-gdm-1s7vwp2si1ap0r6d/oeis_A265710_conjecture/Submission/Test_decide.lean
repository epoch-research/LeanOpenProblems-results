import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

theorem oeis_A265710_conjecture_test :
  ∀ n : ℕ, n > 1 → (a n = 2 ↔ n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) := by
  intro n hn
  constructor
  · intro h
    decide
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · sorry
    · sorry
    · sorry
    · sorry
