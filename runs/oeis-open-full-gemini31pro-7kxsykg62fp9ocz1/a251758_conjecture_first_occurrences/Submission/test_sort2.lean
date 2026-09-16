import Mathlib

def list_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (· ∣ n)

theorem list_divisors_eq_sort (n : ℕ) : 
  list_divisors n = (Nat.divisors n).sort (· ≤ ·) := by sorry

theorem test_dec : list_divisors 15 = [1, 3, 5, 15] := by decide
