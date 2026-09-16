import Mathlib

def my_sum (n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => 0

theorem test_sum : my_sum 4551086841 = 0 := by
  simp [my_sum]
