inductive X (p : Prop) : Prop where
  | intro : (X p → p) → X p
