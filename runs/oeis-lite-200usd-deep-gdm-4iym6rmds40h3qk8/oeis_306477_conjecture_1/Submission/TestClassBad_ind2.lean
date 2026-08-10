class C (α : Type 1) where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type 1) [C α], α → T) → T

def bad : T → False
  | T.mk g =>
    have inst : C T := ⟨bad⟩
    bad (g T inst (T.mk g))
