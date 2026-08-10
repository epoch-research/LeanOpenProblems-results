inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

partial def X : Unsound → Type 0
| Unsound.base => PLift True
| Unsound.mk f => PLift (¬ Nonempty (X (f (Nonempty (X (Unsound.mk f))))))
