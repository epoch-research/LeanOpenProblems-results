import FormalConjectures.Util.ProblemImports
#check ST.Ref
#print ST.Ref
#check ST.Ref.h
#synth Nonempty (ST.Ref PUnit Empty)
#synth Inhabited (ST.Ref PUnit Empty)
example : False := by
  have ne : Nonempty Empty := ST.Ref.h (Classical.choice (show Nonempty (ST.Ref PUnit Empty) by infer_instance))
  cases Classical.choice ne
#print axioms STRefExp._example_1
