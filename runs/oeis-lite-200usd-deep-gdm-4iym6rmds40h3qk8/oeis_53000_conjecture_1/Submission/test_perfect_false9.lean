inductive Unsound : Type 0
| mk : (Prop → Prop) → Unsound

def decomp : Unsound → (Prop → Prop)
| Unsound.mk f => f
