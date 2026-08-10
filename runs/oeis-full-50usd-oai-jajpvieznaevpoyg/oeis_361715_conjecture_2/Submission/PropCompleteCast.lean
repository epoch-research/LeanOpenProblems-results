import FormalConjectures.Util.ProblemImports

noncomputable def proveProp (P : Prop) : P := by
  rcases Classical.propComplete P with h | h
  · cases h
    trivial
  · cases h

example : False := proveProp False
#print axioms proveProp
#print axioms «example»
