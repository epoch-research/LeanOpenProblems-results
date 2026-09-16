import Mathlib
theorem test : (Nat.divisors 4).sort (· ≤ ·) = [1, 2, 4] := by rfl
