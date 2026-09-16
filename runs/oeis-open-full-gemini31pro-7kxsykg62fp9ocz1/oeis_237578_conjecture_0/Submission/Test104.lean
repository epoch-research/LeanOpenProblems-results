import Mathlib

set_option maxRecDepth 200000

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting (10 * 38)) := by
  have : Nat.primeCounting (10 * 38) = 75 := rfl
  rw [this]
  decide
