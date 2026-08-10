inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : Prop → Unsound

def decomp : Unsound → (Type 0 → Unsound)
| Unsound.base p => fun _ => Unsound.base p
| Unsound.mk f => f

theorem unsound_eq : Unsound ↔ (Type 0 → Unsound) := by
  constructor
  · exact decomp
  · exact Unsound.mk

theorem unsound_eq_prop : Unsound = (Type 0 → Unsound) :=
  propext unsound_eq

abbrev U := Unsound

def f_up : U → (Type 0 → U) := cast unsound_eq_prop
def f_down : (Type 0 → U) → U := cast unsound_eq_prop.symm

theorem f_up_down (x : Type 0 → U) : f_up (f_down x) = x := by
  generalize unsound_eq_prop = h
  rcases h with rfl
  rfl

