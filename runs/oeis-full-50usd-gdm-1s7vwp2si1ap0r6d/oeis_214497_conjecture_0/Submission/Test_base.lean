import FormalConjectures.Util.ProblemImports

open Nat

theorem base_case : ∃ k : ℕ, Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) - 1) ∧ Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) + 1) := by
  use 1
  decide

#print axioms base_case