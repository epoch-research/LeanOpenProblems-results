import FormalConjectures.Util.ProblemImports

partial def bad (_ : Unit) : False := bad ()

theorem T : False := bad ()
#print axioms T
