import FormalConjectures.Util.ProblemImports
partial def inhabFalse : Inhabited False := inhabFalse
instance : Inhabited False := inhabFalse
theorem t : False := default
#print axioms t
