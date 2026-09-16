import Mathlib

axiom placeholder : Nat

def f : Nat := 0

theorem conjecture : f = placeholder := sorry

theorem disproof : ¬ (f = placeholder) := by
  intro h
  have : placeholder = placeholder := rfl
  sorry
