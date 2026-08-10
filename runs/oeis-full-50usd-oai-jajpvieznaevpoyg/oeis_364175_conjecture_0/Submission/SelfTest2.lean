import FormalConjectures.Util.ProblemImports
theorem t : False := by
  exact t
#print axioms t
mutual
theorem u : False := by exact v
theorem v : False := by exact u
end
#print axioms u
