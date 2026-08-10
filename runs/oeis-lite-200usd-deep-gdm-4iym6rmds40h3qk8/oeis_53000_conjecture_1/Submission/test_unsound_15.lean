inductive Bad (F : Prop → Prop) : Prop
| mk : (∀ X : Prop, F X) → Bad F

abbrev U := Bad F

def decomp {F : Prop → Prop} : Bad F → (∀ X : Prop, F X)
| Bad.mk f => f

