import Mathlib

partial def partial_decide (P : Prop) : Decidable P :=
  partial_decide P

theorem test_false : False := by
  have h : Decidable False := partial_decide False
  cases h with
  | isTrue h1 => exact h1
  | isFalse h2 => exact h2 (by intro h; exact h)

#print axioms test_false
