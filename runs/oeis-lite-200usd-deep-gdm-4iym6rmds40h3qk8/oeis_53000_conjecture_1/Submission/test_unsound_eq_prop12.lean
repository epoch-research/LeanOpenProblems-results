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

theorem f_up_down (x : Prop → Unsound) : f_up (f_down x) = x := rfl

-- Can we define default using a partial def, but with a Nonempty type first?
-- Since Unsound is equal to Prop → Unsound, can we define a helper function?
-- Let's define a partial def that returns a function:
partial def unsound_fn (u : Unit) : Prop → Unsound :=
  fun _ => f_down (unsound_fn u)

-- Since Prop → Unsound is Unsound, we can get an Unsound!
def default_unsound : Unsound :=
  f_down (unsound_fn ())
