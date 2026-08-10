inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2
| base : Bad2

def decomp : Bad2 → (Type 0 → Bad2)
| Bad2.base => fun _ => Bad2.base
| Bad2.mk1 f => f
