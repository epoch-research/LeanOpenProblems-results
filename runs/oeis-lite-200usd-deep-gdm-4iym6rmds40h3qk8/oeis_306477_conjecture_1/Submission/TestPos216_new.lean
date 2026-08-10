inductive T : Type 1 where
  | base : T
  | mk : ( (X : Type 1) → X → T ) → T
