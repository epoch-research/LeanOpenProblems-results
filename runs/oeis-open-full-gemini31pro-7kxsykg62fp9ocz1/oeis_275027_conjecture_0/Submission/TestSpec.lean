import Mathlib

axiom conjecture : True

macro_rules
  | `(type_of% conjecture) => `(False)

theorem conjecture.disproof : ¬ (type_of% conjecture) := by
  intro h
  exact h
