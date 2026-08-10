inductive Bad4 : Type 1
| mk1 : (Type 0 → Bad4) → Bad4
| base : Bad4

def Bad4_to_Prop : Bad4 → Type 0 → Prop
| Bad4.base, _ => False
| Bad4.mk1 f, X => ¬ (Bad4_to_Prop (f X) X)

def U : Bad4 := Bad4.mk1 (fun X => Bad4.base)

partial def X (u : Unit) : Type 0 :=
  PLift (Bad4_to_Prop U (X u))
