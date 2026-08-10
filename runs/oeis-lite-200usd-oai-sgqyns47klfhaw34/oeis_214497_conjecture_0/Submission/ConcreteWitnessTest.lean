import FormalConjectures.Util.ProblemImports
open Nat

example : ∃ k : ℕ, Nat.Prime ((3 ^ 437 - k) * (2 ^ 437) - 1) ∧ Nat.Prime ((3 ^ 437 - k) * (2 ^ 437) + 1) := by
  use 924789
  native_decide

#print axioms _example
