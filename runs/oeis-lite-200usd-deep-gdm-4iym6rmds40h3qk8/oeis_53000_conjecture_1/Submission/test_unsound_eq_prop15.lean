inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

theorem unsound_eq : Unsound ↔ (Prop → Unsound) := by
  constructor
  · intro u
    cases u with
    | mk f => exact f
  · exact Unsound.mk

open Classical

theorem unsound_eq_prop : Unsound = (Prop → Unsound) :=
  propext unsound_eq

def f_up : Unsound → (Prop → Unsound) := cast unsound_eq_prop
def f_down : (Prop → Unsound) → Unsound := cast unsound_eq_prop.symm

instance : Inhabited Unsound where
  default := f_down (fun _ => default)

partial def bad_fn (u : Unit) : Unsound := bad_fn u

theorem unsound : False := by
  have h_val : Unsound := bad_fn ()
  have h_fn : Prop → Unsound := f_up h_val
  have h_false_unsound : Unsound := h_fn False
  -- wait, h_fn is Prop → Unsound.
  -- can we get False?
  sorry
