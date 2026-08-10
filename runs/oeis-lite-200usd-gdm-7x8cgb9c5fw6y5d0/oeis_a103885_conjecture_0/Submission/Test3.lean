import FormalConjectures.Util.ProblemImports

open Complex

example (x_0 : ℝ) (hx_pos : 0 ≤ x_0) :
    let z : ℂ := ⟨Real.sqrt x_0, 0⟩
    z ^ 2 = algebraMap ℝ ℂ x_0 := by
  intro z
  rw [sq]
  dsimp [z]
  apply Complex.ext
  · simp
    exact Real.mul_self_sqrt hx_pos
  · simp
