inductive Unsound : Prop
| mk : (Unsound → Unsound) → Unsound

def val : Unsound → False
| Unsound.mk f => val (f (Unsound.mk f))

#print axioms val


