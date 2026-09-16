import Mathlib

theorem foo : (Nat.digits 10 (Nat.factorial 5)).count 6 = 0 := by
  dsimp [Nat.digits, Nat.factorial]
  decide
