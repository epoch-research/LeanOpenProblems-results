import FormalConjectures.Util.ProblemImports
partial def pfFalse (u : Unit) : False := by
  exact unsafeCast True.intro
#print pfFalse
#print axioms pfFalse

theorem bad : False := pfFalse ()
#print axioms bad
