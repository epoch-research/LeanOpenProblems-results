import Mathlib.Tactic.NormNum.Prime

-- Let us test some primes of different sizes
theorem prime_test_9d : Nat.Prime 1000000007 := by norm_num
theorem prime_test_10d : Nat.Prime 2000000011 := by norm_num
-- theorem prime_test_11d : Nat.Prime 10000000019 := by norm_num
