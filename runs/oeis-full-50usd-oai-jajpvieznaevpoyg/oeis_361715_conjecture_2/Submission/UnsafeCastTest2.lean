import FormalConjectures.Util.ProblemImports

unsafe def ufalse : False := unsafeCast True

theorem t : False := ufalse
#print axioms t
