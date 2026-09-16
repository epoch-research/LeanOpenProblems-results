import Mathlib

axiom X : Nat

theorem foo : X = 1 := by
  first
  | (unfold X; rfl)
  | sorry
