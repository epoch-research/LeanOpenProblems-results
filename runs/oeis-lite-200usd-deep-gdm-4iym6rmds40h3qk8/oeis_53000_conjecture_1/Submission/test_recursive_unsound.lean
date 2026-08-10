inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

def f (p : Prop) : Unsound := Unsound.mk (fun q => f (p ∧ q))
