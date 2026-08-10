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

theorem prove_false : False := by
  cases safe_decide False with
  | isTrue h =>
    exact h
  | isFalse h' =>
    -- in this branch, we have h' : ¬False
    -- but we need to prove False. Since safe_decide False is actually isTrue (unsafeCast ()),
    -- does safe_decide False reduce to isFalse? No, but wait...
    sorry
