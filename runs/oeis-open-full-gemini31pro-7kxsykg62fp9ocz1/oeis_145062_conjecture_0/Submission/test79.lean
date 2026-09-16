import Mathlib

axiom X : Nat

theorem foo : X = 1 := by
  unfold X
  rfl
