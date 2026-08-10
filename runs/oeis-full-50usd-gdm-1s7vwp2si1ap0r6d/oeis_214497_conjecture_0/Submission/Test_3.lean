import FormalConjectures.Util.ProblemImports

open Nat

theorem case_3 : ∃ k : ℕ, Nat.Prime ((3 ^ 3 - k) * (2 ^ 3) - 1) ∧ Nat.Prime ((3 ^ 3 - k) * (2 ^ 3) + 1) := by
  use 18
  decide
