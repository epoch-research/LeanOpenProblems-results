inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : (X : Type 0) → (X → Unsound) → (Unsound → X) → Unsound
