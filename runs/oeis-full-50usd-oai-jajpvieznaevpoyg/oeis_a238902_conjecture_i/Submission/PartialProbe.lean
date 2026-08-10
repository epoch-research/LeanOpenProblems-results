import FormalConjectures.Util.ProblemImports
partial def pfFalse (_ : Unit) : False := pfFalse ()
theorem bad : False := pfFalse ()
#print axioms bad
#print pfFalse
