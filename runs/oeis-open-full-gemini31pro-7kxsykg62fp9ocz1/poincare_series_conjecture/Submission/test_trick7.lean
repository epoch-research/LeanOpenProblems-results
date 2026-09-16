import Mathlib
axiom c : Nat

theorem conjecture : 0 = c := sorry

theorem conjecture.disproof : ¬ (type_of% @conjecture) :=
  -- If we can't prove it, maybe we use an auxiliary file?
  -- "your submission may split your proof across further .lean files under it"
  sorry
