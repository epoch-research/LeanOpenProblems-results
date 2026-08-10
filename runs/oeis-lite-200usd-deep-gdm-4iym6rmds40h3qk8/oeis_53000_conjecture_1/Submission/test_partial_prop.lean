inductive Unsound : Prop
| mk : (∀ X : Type 0, F X) → Unsound
| base : Unsound

where F (X : Type 0) : Prop := (X → False → False) → X → False

partial def decomp : Unsound → (∀ X : Type 0, F X)
| Unsound.mk f => f
| Unsound.base => decomp Unsound.base
