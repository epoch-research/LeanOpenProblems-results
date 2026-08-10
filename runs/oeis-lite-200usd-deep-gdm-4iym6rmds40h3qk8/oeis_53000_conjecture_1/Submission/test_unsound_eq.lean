inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound

def decomp : Unsound → (Type 0 → Unsound)
| Unsound.mk f => f

theorem unsound_eq : Unsound = (Type 0 → Unsound) := by
  apply propext
  constructor
  · exact decomp
  · exact Unsound.mk
