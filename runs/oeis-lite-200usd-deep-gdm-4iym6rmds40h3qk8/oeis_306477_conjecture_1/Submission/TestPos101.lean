class C (α : Type 1) where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type 1) [C α], T) → T
