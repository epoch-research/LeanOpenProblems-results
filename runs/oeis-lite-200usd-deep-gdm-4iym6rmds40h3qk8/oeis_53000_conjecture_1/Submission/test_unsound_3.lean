inductive Unsound : Type 0
| mk : (Type 0 → Unsound) → Unsound
