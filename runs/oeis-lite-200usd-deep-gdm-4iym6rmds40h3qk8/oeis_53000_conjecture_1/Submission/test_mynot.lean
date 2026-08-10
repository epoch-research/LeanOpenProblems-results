def MyNot (P : Prop) : Prop := P → False

inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : MyNot Unsound → Unsound
