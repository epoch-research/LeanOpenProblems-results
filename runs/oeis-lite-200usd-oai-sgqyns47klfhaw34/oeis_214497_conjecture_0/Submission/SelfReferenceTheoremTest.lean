import FormalConjectures.Util.ProblemImports

 theorem selfFalse : False := by
  exact selfFalse

mutual
  theorem aFalse : False := by exact bFalse
  theorem bFalse : False := by exact aFalse
end

#print axioms selfFalse
#print axioms aFalse
#print axioms bFalse
