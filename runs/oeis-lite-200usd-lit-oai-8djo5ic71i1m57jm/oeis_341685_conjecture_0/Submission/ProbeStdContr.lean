import FormalConjectures.Util.ProblemImports

#synth IsDomain (ℚ × ℚ)
#synth CharP (ZMod 1) 1
#synth Nontrivial (ZMod 1)
#synth CharP PUnit 1
#synth Nontrivial PUnit
#synth NoZeroDivisors (ℚ × ℚ)
#synth IsCancelMulZero (ℚ × ℚ)

example : False := by
  exact false_of_nontrivial_of_product_domain ℚ ℚ

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)
