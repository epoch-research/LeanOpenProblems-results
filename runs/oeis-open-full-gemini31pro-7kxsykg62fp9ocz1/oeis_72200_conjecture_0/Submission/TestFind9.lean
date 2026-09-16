import Mathlib

theorem test2 : Nat.digits 10 6 = [6] := by
  have h1 : 6 < 10 := by decide
  rw [Nat.digits_of_lt 10 6 (by decide) h1]
