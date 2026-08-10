import FormalConjectures.Util.ProblemImports
#synth IsDomain (ℤ × ℤ)
#synth IsDomain (ℚ × ℚ)
#synth IsDomain (ZMod 2 × ZMod 2)
example : False := by
  exact false_of_nontrivial_of_product_domain ℤ ℤ
