import FormalConjectures.Util.ProblemImports
open Nat

-- Try simple candidate families observed computationally: j=3 for n=6,18,... but not general.
example (n : ℕ) (h : n = 6) : ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  subst n; use 3^6 - 3; norm_num

example (n : ℕ) (h : n = 18) : ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  subst n; use 3^18 - 3; norm_num

-- Can norm_num prove very large fixed primality certificates? useful only for finite cases.
example : Nat.Prime (3 * 2^18 - 1) ∧ Nat.Prime (3 * 2^18 + 1) := by norm_num
