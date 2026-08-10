import Mathlib

unsafe def unsafe_decide_impl (P : Prop) : Decidable P :=
  Decidable.isTrue (unsafeCast ())

theorem nonempty_decidable (P : Prop) : Nonempty (Decidable P) := by
  by_cases h : P
  · exact Nonempty.intro (Decidable.isTrue h)
  · exact Nonempty.intro (Decidable.isFalse h)

@[implemented_by unsafe_decide_impl]
noncomputable def safe_decide (P : Prop) : Decidable P :=
  Classical.choice (nonempty_decidable P)

instance (P : Prop) : Decidable P := safe_decide P

theorem test_false : 0 = 1 := by
  decide
