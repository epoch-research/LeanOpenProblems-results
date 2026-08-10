import FormalConjectures.Util.ProblemImports

noncomputable def chooseFalse : False := Classical.choice (show Nonempty False from by infer_instance)

theorem t : False := chooseFalse
#print axioms t
