import FormalConjectures.Util.ProblemImports
#check (show ¬ Squarefree (0:ℤ) by norm_num)
#check (show Squarefree (1:ℤ) by norm_num)
#synth Fact (Squarefree (0:ℤ))
#synth Fact (Squarefree (1:ℤ))
#synth Fact ((0:ℤ) ≠ 1)
#check QuadraticAlgebra.fact_field (d := (0:ℤ))
