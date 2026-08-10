inductive Bad : Type
  | mk : (List Bad → PEmpty) → Bad
