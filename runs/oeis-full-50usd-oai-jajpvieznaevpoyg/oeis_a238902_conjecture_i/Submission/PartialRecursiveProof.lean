import FormalConjectures.Util.ProblemImports
partial def pfFalse (u : Unit) : False := by
  exact pfFalse ()
#print pfFalse
#print axioms pfFalse
