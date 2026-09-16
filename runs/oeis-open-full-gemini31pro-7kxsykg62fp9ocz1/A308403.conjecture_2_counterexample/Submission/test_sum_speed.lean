import Mathlib

def bigSum (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun i =>
    (Finset.range (n + 1)).sum fun j => 0

theorem test_sum : bigSum 1000 = 0 := by native_decide
