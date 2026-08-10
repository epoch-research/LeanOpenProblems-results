import FormalConjectures.Util.ProblemImports
open scoped Polynomial

#check QuadraticAlgebra.instField'
#check QuadraticAlgebra

-- try deriving 0=1 or false from field on QuadraticAlgebra ℚ 0 0
example : (0 : QuadraticAlgebra ℚ 0 0) = 1 := by
  -- if field exists but type maybe nontrivial, no
  norm_num

#print axioms QuadraticAlgebra.instField'
