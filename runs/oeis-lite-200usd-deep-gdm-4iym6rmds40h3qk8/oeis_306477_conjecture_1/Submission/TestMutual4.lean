class C (α : Type) : Prop where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], T) → T

mutual
  def bad : T → False
    | T.mk g => bad (g (ULift T))

  instance instCT : C (ULift T) where
    f := fun x => bad x.down
end
