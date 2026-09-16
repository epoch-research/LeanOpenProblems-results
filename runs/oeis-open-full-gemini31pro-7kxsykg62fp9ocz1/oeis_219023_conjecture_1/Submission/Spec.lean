import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Nat.primesBelow n).sum (fun p =>
    if (n ^ 2 - n + p).Prime ∧ (n ^ 2 + n - p).Prime then 1 else 0
  )

theorem oeis_219023_conjecture_1 (n : ℕ) (h : n > 2732) : a n > 0 := by
  sorry

theorem oeis_219023_conjecture_1.disproof : ¬ (type_of% @oeis_219023_conjecture_1) := by
  sorry
