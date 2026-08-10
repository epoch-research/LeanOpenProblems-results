import FormalConjectures.Util.ProblemImports

def badDef : (n : Nat) → False
| n => badDef n
termination_by n => n
decreasing_by
  exact Nat.lt_irrefl _

theorem badTerm2 : False := badDef 0
#print axioms badTerm2
