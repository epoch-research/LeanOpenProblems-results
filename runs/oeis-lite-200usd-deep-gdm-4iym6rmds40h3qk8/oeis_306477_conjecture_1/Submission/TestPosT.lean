inductive T : Type 1 where
  | mk : ( (T → Prop) → Prop ) → T
