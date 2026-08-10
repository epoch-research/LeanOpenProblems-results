import FormalConjectures.Util.ProblemImports

mutual
  theorem p1 : False := p2
  theorem p2 : False := p1
end

#print axioms p1
