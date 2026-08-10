inductive Unsound : Prop
| mk : (Prop → False) → Unsound

def decomp : Unsound → (Prop → False)
| Unsound.mk f => f
