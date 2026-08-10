inductive MyType (F : Prop → Prop) : Prop
| mk : (∀ X : Prop, F X) → MyType F

def decomp {F : Prop → Prop} : MyType F → (∀ X : Prop, F X)
| MyType.mk f => f
