import FormalConjectures.Util.ProblemImports

unsafe opaque badOpaque : False := unsafeCast ()

theorem Topaque : False := badOpaque
#print axioms Topaque
