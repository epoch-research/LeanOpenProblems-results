import Mathlib

mutual
  inductive F : Type 2 → Type 3 where
    | mk : (α : Type 2) → (α → False) → F α
  inductive Bad : Type 2 → Type 2 where
    | mk : (α : Type 2) → F (Bad α) → Bad α
end







