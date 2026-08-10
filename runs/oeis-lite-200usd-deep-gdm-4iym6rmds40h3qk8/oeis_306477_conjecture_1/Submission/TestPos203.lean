inductive T : Type 1 where
  | base : T
  | mk : (Type → Prop) → T
