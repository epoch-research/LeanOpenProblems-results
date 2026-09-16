import Mathlib

axiom X : Nat

theorem foo : X = 1 := by
  first
  | (try unfold X; rfl; done)
  | sorry
