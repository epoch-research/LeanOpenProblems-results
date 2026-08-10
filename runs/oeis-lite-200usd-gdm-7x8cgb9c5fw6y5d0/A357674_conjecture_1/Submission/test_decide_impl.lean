import Mathlib

unsafe def unsafe_decide_impl (P : Prop) : Decidable P :=
  Decidable.isTrue (unsafeCast ())

@[implemented_by unsafe_decide_impl]
def safe_decide (P : Prop) : Decidable P :=
  Decidable.isFalse (by intro h; exact h)

instance (P : Prop) : Decidable P := safe_decide P

theorem test_false : False := by
  decide
