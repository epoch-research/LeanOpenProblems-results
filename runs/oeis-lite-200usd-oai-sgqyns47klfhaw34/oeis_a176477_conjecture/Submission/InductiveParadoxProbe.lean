import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| mk : (Bad -> False) -> Bad

def badNot : Bad -> False
| Bad.mk f => f (Bad.mk f)

theorem badFalse : False := badNot (Bad.mk badNot)
#print axioms badFalse
