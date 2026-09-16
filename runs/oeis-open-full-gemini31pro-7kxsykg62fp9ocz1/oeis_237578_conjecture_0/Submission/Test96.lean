import Mathlib

theorem check_not_prime : ¬ Nat.Prime (Nat.primeCounting 38) := by
  have : Nat.primeCounting 38 = 12 := rfl
  rw [this]
  decide
