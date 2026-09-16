import Mathlib

theorem test : (Nat.divisors 15).sort (· ≤ ·) = [1, 3, 5, 15] := by decide
