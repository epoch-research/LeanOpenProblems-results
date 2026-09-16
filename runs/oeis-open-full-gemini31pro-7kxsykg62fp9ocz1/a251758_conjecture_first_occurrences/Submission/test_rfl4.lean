import Mathlib
theorem test : (Nat.divisors 4).sort (· ≤ ·) = [1, 2, 4].mergeSort (· ≤ ·) := by rfl
