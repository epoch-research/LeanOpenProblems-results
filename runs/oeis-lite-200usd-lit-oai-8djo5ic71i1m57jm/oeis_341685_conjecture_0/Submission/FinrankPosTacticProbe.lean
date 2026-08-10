import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Module.Free ℚ (Padic 3)
example : 0 < Module.finrank ℚ (Padic 3) := by positivity
example : 0 < Module.finrank ℚ (Padic 3) := by norm_num
example : Module.finrank ℚ (Padic 3) ≠ 0 := by positivity
example : Module.Finite ℚ (Padic 3) := by
  exact Module.finite_of_finrank_pos (R := ℚ) (M := Padic 3) (by positivity)
