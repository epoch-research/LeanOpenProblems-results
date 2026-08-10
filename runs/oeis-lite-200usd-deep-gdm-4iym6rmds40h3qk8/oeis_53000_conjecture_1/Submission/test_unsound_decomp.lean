inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Type 0 → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f
