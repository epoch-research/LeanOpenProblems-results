import FormalConjectures.Util.ProblemImports
open Nat

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - (3^n - 1)) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - (3^n - 1)) * (2 ^ n) + 1) := by
  simp
  fail_if_success norm_num
  fail_if_success omega
  fail_if_success aesop
  admit

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  use (3^n - 1)
  simp
  fail_if_success norm_num
  fail_if_success omega
  fail_if_success aesop
  admit
