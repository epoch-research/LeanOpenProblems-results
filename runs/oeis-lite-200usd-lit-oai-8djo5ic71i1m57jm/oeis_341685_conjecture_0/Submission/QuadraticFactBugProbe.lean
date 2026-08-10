import FormalConjectures.Util.ProblemImports
#check QuadraticAlgebra.fact_field
#check Squarefree
example : ¬ Squarefree (0 : ℤ) := by
  -- try automation
  norm_num [Squarefree]
#synth Fact (Squarefree (0 : ℤ))
#synth Fact ((0 : ℤ) ≠ 1)
example : False := by
  haveI : Fact (Squarefree (0 : ℤ)) := by infer_instance
  haveI : Fact ((0 : ℤ) ≠ 1) := by infer_instance
  have h := (Fact.out : ∀ r : ℚ, r ^ 2 ≠ (0 : ℤ) + 0 * r)
  exact h 0 (by norm_num)
