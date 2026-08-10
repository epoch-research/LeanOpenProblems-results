class C (α : Type) where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], T) → T
