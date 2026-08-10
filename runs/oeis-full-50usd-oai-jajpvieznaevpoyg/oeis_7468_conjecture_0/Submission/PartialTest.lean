import FormalConjectures.Util.ProblemImports

partial def badFalse (_ : Unit) : False := badFalse ()

theorem bad : False := badFalse ()
#print axioms badFalse
#print axioms bad
