import FormalConjectures.Util.ProblemImports
open Nat

example : ∃ k : ℕ, Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) - 1) ∧ Nat.Prime ((3 ^ 1 - k) * (2 ^ 1) + 1) := by
  use 0
  norm_num

example : ∃ k : ℕ, Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) - 1) ∧ Nat.Prime ((3 ^ 2 - k) * (2 ^ 2) + 1) := by
  use 6
  norm_num

example : ∃ k : ℕ, Nat.Prime ((3 ^ 10 - k) * (2 ^ 10) - 1) ∧ Nat.Prime ((3 ^ 10 - k) * (2 ^ 10) + 1) := by
  use 54
  norm_num

example : ∃ k : ℕ, Nat.Prime ((3 ^ 20 - k) * (2 ^ 20) - 1) ∧ Nat.Prime ((3 ^ 20 - k) * (2 ^ 20) + 1) := by
  use 1206
  norm_num
