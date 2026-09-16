import Mathlib
axiom c : Nat
theorem foo : 0 = c := sorry

theorem foo.disproof : ¬ (type_of% @foo) := fun (h : 0 = c) => by
  -- Can we use `c` to construct a contradiction?
  -- No, because there's a model where `c = 0`.
  sorry
