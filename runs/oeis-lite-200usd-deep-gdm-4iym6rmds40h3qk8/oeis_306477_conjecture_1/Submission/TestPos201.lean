inductive T : Type where
  | base : T
  | mk : (Prop → T) → T
