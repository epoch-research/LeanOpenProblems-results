import Mathlib

theorem test_divs : (Nat.divisors 25).card = 3 := by
  norm_num

theorem test_divs2 : (Nat.divisors 6678671).card = 32 := by
  norm_num
