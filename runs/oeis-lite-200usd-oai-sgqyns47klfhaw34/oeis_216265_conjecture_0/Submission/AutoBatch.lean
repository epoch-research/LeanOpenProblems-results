import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

example (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  fail_if_success positivity
  fail_if_success omega
  fail_if_success aesop
  fail_if_success grind
  unfold A216265
  fail_if_success positivity
  fail_if_success omega
  fail_if_success aesop
  fail_if_success grind
  unfold Nat.primeCounting Nat.primeCounting'
  fail_if_success simp
  fail_if_success omega
  fail_if_success aesop
  fail_if_success grind
  sorry
