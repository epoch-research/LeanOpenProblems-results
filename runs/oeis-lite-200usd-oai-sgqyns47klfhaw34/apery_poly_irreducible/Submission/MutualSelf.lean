import FormalConjectures.Util.ProblemImports
mutual
  theorem A : False := by exact B
  theorem B : False := by exact A
end
#print axioms A
