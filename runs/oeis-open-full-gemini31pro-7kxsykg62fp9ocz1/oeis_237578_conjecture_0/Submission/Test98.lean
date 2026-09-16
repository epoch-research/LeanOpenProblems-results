import Mathlib

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting (2 * 38)) := by
  have : Nat.primeCounting (2 * 38) = 21 := rfl
  rw [this]
  decide
