import Mathlib

axiom c : Nat

theorem foo : 0 = c := sorry

theorem foo.disproof : ¬ (type_of% @foo) := by
  intro h
  -- can we prove false?
  sorry
