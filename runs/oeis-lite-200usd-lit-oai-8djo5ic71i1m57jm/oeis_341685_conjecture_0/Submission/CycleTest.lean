import FormalConjectures.Util.ProblemImports
mutual
  theorem t : False := by exact u
  theorem u : False := by exact t
end
#print axioms t
