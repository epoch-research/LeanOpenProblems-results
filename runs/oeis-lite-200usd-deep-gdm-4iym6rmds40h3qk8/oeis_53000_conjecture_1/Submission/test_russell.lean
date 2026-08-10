inductive Bad : Prop
| mk : (Bad → False) → Bad
