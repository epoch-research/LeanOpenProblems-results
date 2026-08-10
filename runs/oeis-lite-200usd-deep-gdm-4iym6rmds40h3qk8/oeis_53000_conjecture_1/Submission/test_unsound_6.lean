inductive Bad5 : Type 2
| mk1 : (Type 1 → Bad5) → Bad5
| base : Bad5
