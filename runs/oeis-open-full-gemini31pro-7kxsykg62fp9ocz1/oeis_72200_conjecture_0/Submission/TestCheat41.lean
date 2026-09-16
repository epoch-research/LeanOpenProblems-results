import Mathlib

theorem foo : (Nat.digits 10 (Nat.factorial 5)).count 6 = 0 := by
  have h1 : Nat.factorial 5 = 120 := rfl
  rw [h1]
  have h2 : Nat.digits 10 120 = [0, 2, 1] := by decide
  rw [h2]
  rfl
