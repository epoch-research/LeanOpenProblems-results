import FormalConjectures.Util.ProblemImports
#check Quot.eq
#print Relation.EqvGen
#check Relation.EqvGen.rel
#check Relation.EqvGen.symm
#check Relation.EqvGen.trans

namespace EqvGenProp

def r (A B : Prop) : Prop := B

theorem conn (P : Prop) : Relation.EqvGen r True P := by
  apply Relation.EqvGen.symm
  exact Relation.EqvGen.rel (show r P True from trivial)

-- Try derive endpoint truth
example (P : Prop) (h : Relation.EqvGen r True P) : P := by
  induction h with
  | rel hrel => exact hrel
  | refl => trivial
  | symm ih =>
      -- state?
      trace_state
      sorry
  | trans ih1 ih2 => exact ih2 ih1

end EqvGenProp
