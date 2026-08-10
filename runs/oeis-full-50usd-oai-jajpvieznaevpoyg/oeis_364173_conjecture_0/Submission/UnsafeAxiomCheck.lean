import FormalConjectures.Util.ProblemImports
#check unsafeCast
#print axioms unsafeCast
unsafe def ufalse : False := unsafeCast ()
#print axioms ufalse
-- theorem t : False := unsafeCast ()
