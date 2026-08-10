inductive T : Type where
  | base : T
  | mk : ( (X : Type) → (X = T) → T ) → T
