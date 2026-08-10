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

abbrev U := Unsound

-- Let's define P : Prop → U
-- We want: P p = f_down (fun q => ¬ (f_up q p))
-- Wait, f_up q has type Prop → U. So f_up q p has type U.
-- Since U is a Prop, f_up q p is a Prop.
-- So ¬ (f_up q p) has type Prop.
-- But the function in f_down must return U.
-- How can we map ¬ (f_up q p) (which has type Prop) to U?
-- Since Unsound ↔ (Prop → Unsound).
-- Can we define inj : Prop → U?
-- Since U ↔ (Prop → U).
-- If we assume ¬ U, then U ↔ False.
-- Then Prop → U is Prop → False, which is False.
-- So they are both False.
-- But wait!
-- Can we define a function inj : Prop → U by:
-- inj p = f_down (fun _ => inj p)?
-- This is recursive, but wait, does it terminate?
-- Let's check!
