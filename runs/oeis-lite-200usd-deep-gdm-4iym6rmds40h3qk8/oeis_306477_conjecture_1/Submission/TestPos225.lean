class C (α : Type u) where
  f : α → False

inductive T : Type u where
  | mk : (∀ (α : Type u) [C α], T) → T
