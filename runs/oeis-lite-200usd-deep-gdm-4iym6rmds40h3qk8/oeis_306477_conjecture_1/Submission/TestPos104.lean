inductive T : Type 1 where
  | mk : (∀ (α : Type), (α → T) → T) → T
