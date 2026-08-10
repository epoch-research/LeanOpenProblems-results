import FormalConjectures.Util.ProblemImports
open Nat

-- Some candidate fixed choices; automation confirms they are not symbolic truths.
example (n : ℕ) (hn : n > 0) :
    Nat.Prime (((3 ^ n - (3 ^ n - 1)) * (2 ^ n) - 1)) ∧
    Nat.Prime (((3 ^ n - (3 ^ n - 1)) * (2 ^ n) + 1)) := by
  simp
  try norm_num
  fail

example (n : ℕ) (hn : n > 0) :
    Nat.Prime (((3 ^ n - 0) * (2 ^ n) - 1)) ∧
    Nat.Prime (((3 ^ n - 0) * (2 ^ n) + 1)) := by
  simp
  try norm_num
  fail
