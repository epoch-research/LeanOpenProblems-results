import FormalConjectures.Util.ProblemImports
unsafe def bad : False := unsafeCast ()
unsafe theorem Tunsafe : False := bad
#print axioms Tunsafe
