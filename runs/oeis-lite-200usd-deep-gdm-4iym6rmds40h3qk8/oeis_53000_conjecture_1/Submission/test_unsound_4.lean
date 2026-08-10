set_option bootstrap.inductive_universe_restriction false

inductive Bad3 : Type 1
| mk1 : (Type 1 → Bad3) → Bad3

