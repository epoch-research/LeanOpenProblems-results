import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

def a (n : ℕ) : ℕ :=
  (Nat.factorization n).support.sum fun p =>
    2 ^ (Nat.primeCounting p - 1)

theorem oeis_87207_conjecture_0 :
  ∀ n : ℕ, ∃ k : ℕ, (a^[k]) n = 0 := by
  sorry

theorem oeis_87207_conjecture_0.disproof : ¬ (∀ n : ℕ, ∃ k : ℕ, (a^[k]) n = 0) := by
  sorry
