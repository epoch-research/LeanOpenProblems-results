class C (α : Type 1) where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type 1) [C α], Nonempty α → T) → T

def bad : T → False
  | T.mk g =>
    have inst : C T := ⟨bad⟩
    have h_ne : Nonempty T := ⟨T.mk g⟩
    bad (g T inst h_ne)
