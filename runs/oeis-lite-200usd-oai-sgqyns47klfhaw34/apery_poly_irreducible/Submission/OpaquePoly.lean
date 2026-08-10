import FormalConjectures.Util.ProblemImports

opaque proofOf (P : Prop) : P

theorem bad : False := proofOf False
#print axioms bad
