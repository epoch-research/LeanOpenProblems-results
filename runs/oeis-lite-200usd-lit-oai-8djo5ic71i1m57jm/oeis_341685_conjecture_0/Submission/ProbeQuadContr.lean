import FormalConjectures.Util.ProblemImports
open QuadraticAlgebra

#check QuadraticAlgebra.instField'
#check QuadraticAlgebra.instIsQuadraticExtension
#check Algebra.IsQuadraticExtension.to_numberField
#synth Field (QuadraticAlgebra ℚ 0 0)
#synth Field (QuadraticAlgebra ℚ 1 0)
#synth Fact (∀ r : ℚ, r ^ 2 ≠ (0:ℚ) + 0 * r)
#synth Fact (∀ r : ℚ, r ^ 2 ≠ (1:ℚ) + 0 * r)

example : False := by
  -- see if field on reducible algebra is available
  let A := QuadraticAlgebra ℚ (0:ℚ) (0:ℚ)
  fail_if_success haveI : Field A := inferInstance
  guard_target = False
  sorry
