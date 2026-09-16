import Mathlib

theorem check_21 : ¬ Nat.Prime (Nat.primeCounting (21 * 38)) := by
  have : Nat.primeCounting (21 * 38) = 139 := by decide
  rw [this]
  decide
