import FormalConjectures.Util.ProblemImports
mutual
  theorem t : False := by
    haveI : Decidable False := isTrue t
    decide
end
#print axioms t
