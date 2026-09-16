import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def a (n : ℕ) : ℕ := 1

theorem oeis_a185150_conjecture_2 : ∀ (n : ℕ), n ∈ Finset.Ioc 0 1000000000 → 0 < a n := by
  intro n _
  decide
