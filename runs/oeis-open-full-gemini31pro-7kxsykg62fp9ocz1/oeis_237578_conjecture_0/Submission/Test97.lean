import Mathlib

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting (20 * 38)) := by
  have : Nat.primeCounting (20 * 38) = 134 := rfl
  rw [this]
  decide
