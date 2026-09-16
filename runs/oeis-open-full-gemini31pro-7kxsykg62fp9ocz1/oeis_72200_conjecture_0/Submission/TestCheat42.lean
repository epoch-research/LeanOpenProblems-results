import Mathlib

theorem foo : (Nat.digits 10 (Nat.factorial 5)).count 6 = 0 := by
  have h1 : Nat.factorial 5 = 120 := rfl
  rw [h1]
  rw [Nat.digits_def', Nat.digits_def', Nat.digits_def', Nat.digits_zero]
  rfl
