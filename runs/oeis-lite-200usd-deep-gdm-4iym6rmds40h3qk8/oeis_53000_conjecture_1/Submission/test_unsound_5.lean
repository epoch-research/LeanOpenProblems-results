inductive Bad4 : Type 1
| mk1 : (Type 0 → Bad4) → Bad4
| base : Bad4
