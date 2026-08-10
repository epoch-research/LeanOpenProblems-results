class C (α : Prop) where
  f : α → False

inductive T : Prop where
  | mk : (∀ (α : Prop) [C α], T) → T

mutual
  def bad : T → False
    | T.mk g => bad (@g T instCT)

  def g (α : Prop) [inst : C α] : T :=
    T.mk g

  instance instCT : C T where
    f := bad
end

theorem false_proof : False := bad (@g T instCT)
