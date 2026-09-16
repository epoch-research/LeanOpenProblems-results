import Mathlib

set_option maxRecDepth 2000000

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting (20 * 38)) := by
  have : Nat.primeCounting (20 * 38) = 134 := rfl
  rw [this]
  decide
