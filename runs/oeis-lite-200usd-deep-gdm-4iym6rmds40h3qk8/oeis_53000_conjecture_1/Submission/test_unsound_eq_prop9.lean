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

-- Can we prove Nonempty Unsound?
-- Let's see: Unsound = (Prop → Unsound).
-- If we assume ¬ Nonempty Unsound, can we get a contradiction?
-- Actually, if ¬ Nonempty Unsound, then Unsound is empty (i.e. Unsound ↔ False).
-- But Unsound ↔ (Prop → Unsound).
-- If Unsound ↔ False, then (Prop → Unsound) ↔ False.
-- But Prop → Unsound is Prop → False, which is ¬ Prop.
-- Is ¬ Prop ↔ False?
-- No, because ¬ Prop is (Prop → False). There are props that are false, but is (Prop → False) false?
-- Prop → False means all props are false, which is false (since True is a Prop and is true).
-- So (Prop → False) ↔ False is indeed true!
-- So if Unsound ↔ False, then both sides are False, which is consistent!
-- So we cannot prove Nonempty Unsound just from this.
-- But wait!
-- What if we use a partial def to get Nonempty Unsound?
-- Since Nonempty is in Prop, `partial def` cannot be used to prove Prop directly.
-- But we can define a partial def of type Unsound!
-- Wait, `partial def` of type Unsound is allowed because Unsound is a Prop, so its sort is Prop (which is Sort 0).
-- But wait, Lean's `partial def` requires the return type to be inhabited.
-- Is `Unsound` inhabited?
-- We can declare:
-- instance : Inhabited Unsound where
--   default := f_down (fun _ => default)
-- Wait! Is this definition of Inhabited Unsound accepted by Lean?
-- Let's test this!
