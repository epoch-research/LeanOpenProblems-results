import Mathlib
open Finset

theorem t1 : (Nat.divisors 15) = {1, 3, 5, 15} := by decide

theorem t2 : ({1, 3, 5, 15} : Finset ℕ).sort (· ≤ ·) = [1, 3, 5, 15] := by
  decide
