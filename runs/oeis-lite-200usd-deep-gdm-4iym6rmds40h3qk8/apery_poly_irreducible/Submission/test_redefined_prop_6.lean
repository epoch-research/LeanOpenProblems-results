inductive T : Bool → Prop → Prop
| base : T false True
| mk : (a : Prop) → T false (¬ a) → T true a
| mk2 : (a : Prop) → T true a → T false a
