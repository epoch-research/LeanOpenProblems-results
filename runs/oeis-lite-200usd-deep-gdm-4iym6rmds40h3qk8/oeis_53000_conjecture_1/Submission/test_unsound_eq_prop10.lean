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

-- Let's define the Inhabited instance recursively!
instance inst_unsound : Inhabited Unsound where
  default := f_down (fun _ => inst_unsound.default)
