import Mathlib

axiom placeholder : Nat

def f : Nat := 0

theorem conjecture : f = placeholder := sorry

theorem conjecture.disproof : ¬ (type_of% @conjecture) := by
  intro h
  sorry
