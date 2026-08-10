inductive T : Type 1 where
  | base : T
  | mk : ( (X : Type) → X → T ) → T
