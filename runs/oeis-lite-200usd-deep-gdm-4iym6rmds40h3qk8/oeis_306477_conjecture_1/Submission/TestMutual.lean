class C (α : Type 1) where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type 1) [C α], T) → T

mutual
  def bad : T → False
    | T.mk g => bad (g T)

  instance instCT : C T where
    f := bad
end

