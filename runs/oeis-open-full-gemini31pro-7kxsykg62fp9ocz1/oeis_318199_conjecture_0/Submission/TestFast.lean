import Mathlib

def my_sum (n : ℕ) : ℕ :=
  if n = 0 then 0 else n + my_sum (n - 1)

theorem test_sum : my_sum 1000 = 500500 := by decide
