inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk f => ∀ p, proj (f p)
