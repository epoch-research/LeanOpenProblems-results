inductive MyType : Type 0
| mk : (Type 0 → MyType) → MyType
| base : MyType
