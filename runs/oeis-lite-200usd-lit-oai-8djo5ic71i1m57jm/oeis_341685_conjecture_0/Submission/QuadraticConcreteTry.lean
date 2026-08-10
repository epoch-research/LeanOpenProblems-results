import FormalConjectures.Util.ProblemImports
open QuadraticAlgebra

#synth Field (QuadraticAlgebra ℚ 0 0)
#synth Field (QuadraticAlgebra ℚ 1 0)
#synth Field (QuadraticAlgebra ℚ 4 0)
#synth Field (QuadraticAlgebra ℚ 2 0)
#synth Fact (Squarefree (0:ℤ))
#synth Fact (Squarefree (1:ℤ))
#synth Fact (Squarefree (4:ℤ))
#synth Fact (Squarefree (2:ℤ))

example : False := by
  let x : QuadraticAlgebra ℚ 0 0 := ⟨0,1⟩
  have hx : x * x = 0 := by ext <;> norm_num [x, mul_def]
  have hxne : x ≠ 0 := by intro h; have := congrArg snd h; norm_num [x] at this
  have : IsUnit x := by
    exact isUnit_of_mul_eq_one ?_
  sorry
