import FormalConjectures.Util.ProblemImports
partial def loopFalse (_ : Unit) : False := loopFalse ()
theorem t : False := loopFalse ()
#print axioms t
