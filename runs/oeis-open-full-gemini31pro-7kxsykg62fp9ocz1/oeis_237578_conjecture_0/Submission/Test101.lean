import Mathlib

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting (3 * 38)) := by
  have : Nat.primeCounting (3 * 38) = 30 := by decide
  rw [this]
  decide
