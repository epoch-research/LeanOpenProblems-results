inductive MyType : Prop
| mk : (Type 0 → MyType) → MyType

def decomp : MyType → (Type 0 → MyType)
| MyType.mk f => f
