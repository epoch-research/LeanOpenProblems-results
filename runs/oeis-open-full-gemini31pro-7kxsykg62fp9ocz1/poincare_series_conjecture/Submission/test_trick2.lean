import Mathlib

axiom c : Nat

theorem foo : 0 = c := sorry

theorem foo.disproof : ¬ (type_of% @foo) := by
  -- We prove ¬ (0 = c) where c is an axiom. But c could be 0, so this is unprovable in general.
  -- The prompt states:
  -- "The file states two theorems, each with a `sorry` proof: the conjecture itself, and a `.disproof` theorem stating exactly its negation. Replace the `sorry` of exactly one of them with a complete proof"
  sorry
