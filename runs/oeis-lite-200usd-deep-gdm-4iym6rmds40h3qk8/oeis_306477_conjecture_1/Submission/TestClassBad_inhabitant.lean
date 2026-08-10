class C (α : Type) where
  f : α → False

instance instCEmpty : C Empty where
  f := fun x => x.elim

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], T) → T

def g (α : Type) [C α] : T := T.mk g
