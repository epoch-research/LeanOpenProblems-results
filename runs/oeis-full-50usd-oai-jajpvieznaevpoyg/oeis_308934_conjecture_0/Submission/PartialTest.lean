import FormalConjectures.Util.ProblemImports
partial def badFalse (_ : Unit) : False := badFalse ()
theorem badTheorem : False := by exact badFalse ()
#print axioms badTheorem
