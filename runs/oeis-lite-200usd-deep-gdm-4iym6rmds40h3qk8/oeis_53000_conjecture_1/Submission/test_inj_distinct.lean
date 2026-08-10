inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Type 0 → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

theorem unsound_eq : Unsound = (Type 0 → Unsound) := by
  apply propext
  constructor
  · exact decomp
  · exact Unsound.mk

abbrev U := Unsound

def f_up : U → (Type 0 → U) := cast unsound_eq
def f_down : (Type 0 → U) → U := cast unsound_eq.symm

theorem base_ne_mk (f : Type 0 → U) : Unsound.base = Unsound.mk f → False := by
  intro h
  -- Can we prove this?
  cases h
