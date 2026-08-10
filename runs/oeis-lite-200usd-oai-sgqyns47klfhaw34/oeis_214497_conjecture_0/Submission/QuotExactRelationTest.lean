import FormalConjectures.Util.ProblemImports

-- If arbitrary Quot equality implied the original relation, this would prove False.
def rFalse (_ _ : Bool) : Prop := False

example : ¬ (Quot.mk rFalse false = Quot.mk rFalse true) := by
  intro h
  have hg : Relation.EqvGen rFalse false true := (Quot.eq).mp h
  induction hg with
  | rel x y hr => exact hr
  | refl x => cases x <;> simp at *
  | symm x y _ ih => exact ih
  | trans x y z _ _ ih1 ih2 => cases x <;> cases z <;> try simp at *; exact ih1

#check Quot.eq
#print axioms Quot.eq
