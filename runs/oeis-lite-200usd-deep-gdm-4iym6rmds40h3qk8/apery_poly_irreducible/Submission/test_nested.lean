def MyNeg (α : Type) : Type := (α → Prop) → Prop

inductive T : Type
| mk : MyNeg T → T

