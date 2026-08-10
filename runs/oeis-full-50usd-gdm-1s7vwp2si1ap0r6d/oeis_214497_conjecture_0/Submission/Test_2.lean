import FormalConjectures.Util.ProblemImports

open Nat

theorem case_2 : ∃ k : ℕ, Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) - 1) ∧ Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) + 1) := by
  use 8
  decide
