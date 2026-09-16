import Mathlib
open Finset

def list_divs (n : ℕ) : List ℕ :=
  ((Nat.divisors n).toList).mergeSort (· ≤ ·)

theorem test : list_divs 15 = [1, 3, 5, 15] := by decide
