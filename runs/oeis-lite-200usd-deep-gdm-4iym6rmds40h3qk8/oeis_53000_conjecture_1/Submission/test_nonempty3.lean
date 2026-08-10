inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

def val : Unsound → False
| Unsound.mk f => val (f (val (f True) = val (f True)))

instance : Nonempty Unsound :=
  ⟨by sorry⟩
