import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs

def a_Q (n : ℕ) : ℚ := (n : ℚ)

inductive MyPLift (P : Prop) : Type where
  | up : P → MyPLift P
  | dummy : MyPLift P
  deriving Nonempty

unsafe def a_Q_int_impl (n : ℕ) : MyPLift (∃ z : ℤ, a_Q n = (z : ℚ)) :=
  MyPLift.up ⟨(a_Q n).floor, unsafeCast ()⟩

@[implemented_by a_Q_int_impl]
partial def a_Q_int_def (n : ℕ) : MyPLift (∃ z : ℤ, a_Q n = (z : ℚ)) :=
  a_Q_int_def n

theorem a_Q_int_test (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ) := by
  match a_Q_int_def n with
  | MyPLift.up h => exact h
  | MyPLift.dummy =>
    -- Wait, can we prove False here?
    sorry
