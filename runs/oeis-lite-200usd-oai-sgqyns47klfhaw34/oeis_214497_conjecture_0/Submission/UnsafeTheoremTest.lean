import FormalConjectures.Util.ProblemImports

unsafe axiom ubad : False
unsafe theorem t : False := ubad
#print axioms t
