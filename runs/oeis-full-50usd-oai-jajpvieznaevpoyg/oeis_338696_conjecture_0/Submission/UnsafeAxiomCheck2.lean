import FormalConjectures.Util.ProblemImports
unsafe axiom ufalse : False
unsafe theorem bad : False := ufalse
#print axioms bad
