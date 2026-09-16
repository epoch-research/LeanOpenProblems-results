import Mathlib

axiom c : Nat

theorem foo : 0 = c := sorry

theorem foo.disproof : ¬ (type_of% @foo) := by
  intro h
  sorry
#print axioms foo.disproof
