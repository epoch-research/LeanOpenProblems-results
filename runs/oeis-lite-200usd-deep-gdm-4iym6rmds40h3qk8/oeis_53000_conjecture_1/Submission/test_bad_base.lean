inductive Bad : Prop
| mk : (Type 0 → Bad) → Bad
| base : PLift (Bad → False) → Bad
