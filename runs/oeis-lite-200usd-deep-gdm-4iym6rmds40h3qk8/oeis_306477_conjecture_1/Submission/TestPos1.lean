inductive T : Type where
  | mk : ((T → Prop) → T) → T
