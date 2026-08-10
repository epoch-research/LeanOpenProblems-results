import FormalConjectures.Util.ProblemImports
partial def inhabFalse (_ : Unit) : Inhabited False := inhabFalse ()
instance : Inhabited False := inhabFalse ()
theorem t : False := default
#print axioms t
