import Mathlib

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting (4 * 38)) := by
  have : Nat.primeCounting (4 * 38) = 36 := rfl
  rw [this]
  decide
