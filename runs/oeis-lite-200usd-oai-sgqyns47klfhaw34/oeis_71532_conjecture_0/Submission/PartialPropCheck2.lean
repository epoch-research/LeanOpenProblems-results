import FormalConjectures.Util.ProblemImports

partial def L (_ : Unit) : Prop := ¬ L ()
#print axioms L
#print L
example : L () ↔ ¬ L () := by
  unfold L
  rfl
example : False := by
  have h : L () ↔ ¬ L () := by unfold L; rfl
  have nl : ¬ L () := fun l => (h.mp l) l
  exact nl (h.mpr nl)
#print axioms PartialPropCheck2._example_2
