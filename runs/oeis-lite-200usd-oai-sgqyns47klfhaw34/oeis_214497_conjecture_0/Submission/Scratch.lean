import FormalConjectures.Util.ProblemImports

open Nat

#check Nat.prime_two
#check Nat.Prime.eq_two_or_odd
#check Nat.Prime
#check Nat.prime_iff
#check norm_num

example : Nat.Prime 3 := by norm_num
example : Nat.Prime 5 := by norm_num

example (n : ℕ) (hn : n = 1) : ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  subst n
  use 0
  norm_num

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  aesop
