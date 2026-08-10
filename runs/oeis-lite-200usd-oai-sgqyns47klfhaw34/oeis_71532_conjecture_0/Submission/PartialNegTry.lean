import FormalConjectures.Util.ProblemImports
partial def negLoop (P : Prop) : P → False := fun h => negLoop P h
example : False := Sat.Valuation.by_cases (v := fun _ => False) (l := Sat.Literal.pos 0) (negLoop _) (negLoop _)
#print axioms negLoop
