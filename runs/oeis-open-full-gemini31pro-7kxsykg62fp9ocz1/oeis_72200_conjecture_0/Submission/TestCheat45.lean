import Mathlib

theorem foo : (Nat.digits 10 (Nat.factorial 5)).count 6 = 0 := by
  have h1 : Nat.factorial 5 = 120 := rfl
  rw [h1]
  have h2 : Nat.digits 10 120 = [0, 2, 1] := by
    rw [Nat.digits_def' (by decide) (by decide)]
    rw [Nat.digits_def' (by decide) (by decide)]
    have hlt : 1 < 10 := by decide
    rw [Nat.digits_of_lt 10 1 (by decide) hlt]
  rw [h2]
  rfl
