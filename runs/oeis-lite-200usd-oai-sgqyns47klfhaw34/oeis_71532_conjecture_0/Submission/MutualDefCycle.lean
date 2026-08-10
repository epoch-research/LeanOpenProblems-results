import FormalConjectures.Util.ProblemImports

mutual
  def p1 : False := p2
  def p2 : False := p1
end

#print axioms p1
