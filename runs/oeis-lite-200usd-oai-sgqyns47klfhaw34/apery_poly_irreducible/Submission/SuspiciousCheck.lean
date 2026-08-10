import FormalConjectures.Util.ProblemImports
#check (show ¬ Squarefree (0:ℤ) from by decide)
#check (show Squarefree (-1:ℤ) from by decide)
#check QuadraticAlgebra.fact_field
#print axioms QuadraticAlgebra.fact_field
example : ¬ Fact (Squarefree (0:ℤ)) := by
  intro h
  have hs : ¬ Squarefree (0:ℤ) := by decide
  exact hs h.out
