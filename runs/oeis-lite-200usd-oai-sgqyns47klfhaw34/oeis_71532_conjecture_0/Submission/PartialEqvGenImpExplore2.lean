import FormalConjectures.Util.ProblemImports

def impRel (p q : Prop) := p → q

partial def egImp {p q : Prop} (h : Relation.EqvGen impRel p q) : p → q := by
  intro hp
  induction h with
  | rel x y hxy => exact hxy hp
  | refl x => exact hp
  | trans x y z hxy hyz ih1 ih2 => exact ih2 (ih1 hp)
  | symm x y hxy ih =>
      exact egImp (Relation.EqvGen.symm x y hxy) hp

#check egImp
#print axioms egImp
