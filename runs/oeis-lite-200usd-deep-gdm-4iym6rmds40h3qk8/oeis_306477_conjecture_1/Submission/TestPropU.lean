inductive U : Prop where
  | base : U
  | mk : (Prop → U) → U
