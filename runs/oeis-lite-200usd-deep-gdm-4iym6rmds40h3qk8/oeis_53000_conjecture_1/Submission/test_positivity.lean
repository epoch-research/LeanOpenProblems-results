inductive Unsound : Type 0
| mk : (((Unsound → Prop) → Prop) → Unsound) → Unsound
