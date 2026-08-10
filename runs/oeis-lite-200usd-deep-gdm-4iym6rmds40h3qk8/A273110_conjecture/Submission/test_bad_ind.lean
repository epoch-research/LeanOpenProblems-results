inductive Bad where
  | mk : List (Bad → False) → Bad
