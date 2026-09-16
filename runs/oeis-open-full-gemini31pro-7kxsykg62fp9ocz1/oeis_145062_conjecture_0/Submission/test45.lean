import Mathlib

axiom X : Nat

theorem H : ¬ (X = 1 ∧ X = 2) := by
  intro h
  have h1 : X = 1 := h.1
  have h2 : X = 2 := h.2
  rw [h1] at h2
  contradiction
#print axioms H
