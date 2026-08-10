inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound

def decomp : Unsound → (Type 0 → Unsound)
| Unsound.mk f => f

theorem unsound_eq : Unsound = (Type 0 → Unsound) := by
  apply propext
  constructor
  · exact decomp
  · exact Unsound.mk

abbrev U := Unsound

def f_up : U → (Type 0 → U) := cast unsound_eq
def f_down : (Type 0 → U) → U := cast unsound_eq.symm

theorem f_up_down (x : Type 0 → U) : f_up (f_down x) = x := by
  dsimp [f_up, f_down]
  generalize unsound_eq = h
  cases h
  rfl
