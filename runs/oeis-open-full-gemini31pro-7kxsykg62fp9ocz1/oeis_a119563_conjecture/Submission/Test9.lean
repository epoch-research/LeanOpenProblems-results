import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1

theorem oeis_a119563_conjecture : {n : ℕ | Nat.Prime (a n)}.Infinite := by sorry

local macro_rules | `(type_of% $_) => `(False)

theorem oeis_a119563_conjecture.disproof : ¬ (type_of% @oeis_a119563_conjecture) := by
  exact id
