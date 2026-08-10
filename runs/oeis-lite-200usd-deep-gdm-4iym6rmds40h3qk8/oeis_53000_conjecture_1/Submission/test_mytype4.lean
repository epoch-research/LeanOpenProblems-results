inductive MyType (F : Type 0 → Prop) : Prop
| mk : (∀ X : Type 0, F X) → MyType F

def decomp {F : Type 0 → Prop} : MyType F → (∀ X : Type 0, F X)
| MyType.mk f => f
