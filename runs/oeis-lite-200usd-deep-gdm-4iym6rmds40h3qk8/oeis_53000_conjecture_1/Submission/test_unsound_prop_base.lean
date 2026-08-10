inductive MyPLift (α : Sort u) : Prop
| up : α → MyPLift α

inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : MyPLift (Unsound → False) → Unsound
