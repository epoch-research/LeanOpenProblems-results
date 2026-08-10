import Mathlib

def T (k' : ℕ) : Type := PLift (Nonempty (k' ≠ 4) ∨ (k' = 4))

theorem T_unique (k' : ℕ) (x y : T k') : x = y := by
  cases x
  cases y
  rfl


