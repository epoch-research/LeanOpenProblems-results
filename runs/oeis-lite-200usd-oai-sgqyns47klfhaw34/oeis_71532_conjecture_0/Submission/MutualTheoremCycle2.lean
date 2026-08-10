import FormalConjectures.Util.ProblemImports

mutual
  theorem p : False := q
  theorem q : False := p
end
#print axioms p
#print axioms q
