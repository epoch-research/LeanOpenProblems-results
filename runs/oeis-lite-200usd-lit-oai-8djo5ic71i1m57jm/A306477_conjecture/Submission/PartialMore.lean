import FormalConjectures.Util.ProblemImports

partial def loopEmpty : Empty := loopEmpty
#print loopEmpty
#print axioms loopEmpty

partial def loopSubtype : {n : Nat // False} := loopSubtype
#print loopSubtype
#print axioms loopSubtype

def badFalse : False := loopEmpty.elim
#print axioms badFalse
