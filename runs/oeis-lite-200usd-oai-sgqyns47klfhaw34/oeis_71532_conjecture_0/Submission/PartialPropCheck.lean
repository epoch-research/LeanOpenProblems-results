import FormalConjectures.Util.ProblemImports

partial def L : Prop := ¬ L
#print axioms L
#print L
example : L ↔ ¬ L := by
  unfold L
  rfl
example : False := by
  have h : L ↔ ¬ L := by unfold L; rfl
  have nl : ¬ L := fun l => (h.mp l) l
  exact nl (h.mpr nl)
#print axioms PartialPropCheck._example_2
