inductive Bad_zero : Type 1
| mk : (Bad_zero → Type 0) → Bad_zero
| base : Bad_zero
