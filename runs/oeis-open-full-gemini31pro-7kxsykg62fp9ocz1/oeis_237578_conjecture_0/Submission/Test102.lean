import Mathlib

set_option maxRecDepth 20000

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting (3 * 38)) := by
  have : Nat.primeCounting (3 * 38) = 30 := rfl
  rw [this]
  decide
