inductive Unsound : Type 0
| mk : (PLift Unsound → Prop) → Unsound

def decomp : Unsound → (PLift Unsound → Prop)
| Unsound.mk f => f
