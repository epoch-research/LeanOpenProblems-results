inductive Ind : Prop
  | mk : (Ind → False) → Ind
