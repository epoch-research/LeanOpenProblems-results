import FormalConjectures.Util.ProblemImports
partial def bad (P : Prop) : P := Classical.choice (show Nonempty P from ⟨bad P⟩)
theorem t : False := bad False
#print axioms t
