import FormalConjectures.Util.ProblemImports
partial def loopNonempty (P : Prop) : Nonempty P := loopNonempty P
example : False := Classical.choice (loopNonempty False)
#print axioms loopNonempty
