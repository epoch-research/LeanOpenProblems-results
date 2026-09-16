import Mathlib

axiom c : Nat

theorem foo : 0 = c := sorry

theorem foo.disproof : ¬ (type_of% @foo) := by
  intro (h : 0 = c)
  have : c = c := rfl
  sorry
