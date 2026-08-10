import FormalConjectures.Util.ProblemImports

unsafe def badUnsafe : False := unsafeCast ()
unsafe theorem badUnsafeThm : False := unsafeCast ()
#print axioms badUnsafe
#print axioms badUnsafeThm
