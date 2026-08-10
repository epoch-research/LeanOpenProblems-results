import FormalConjectures.Util.ProblemImports
open Nat

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - (3^n - 1)) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - (3^n - 1)) * (2 ^ n) + 1) := by
  simp
  norm_num
