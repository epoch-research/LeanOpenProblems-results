inductive Unsound : Type 0
| mk : (Unsound → Prop) → Unsound
