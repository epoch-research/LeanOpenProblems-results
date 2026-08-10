class C (α : Type) where
  f : α → False

instance instCEmpty : C Empty where
  f := fun x => x.elim

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], T) → T

def bad : T → False
  | T.mk g => bad (g Empty)

#print axioms false_proof

