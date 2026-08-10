class C (α : Type) where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], α → T) → T

def bad : T → False
  | T.mk g =>
    have inst : C T := ⟨bad⟩
    bad (g T inst (T.mk g))
