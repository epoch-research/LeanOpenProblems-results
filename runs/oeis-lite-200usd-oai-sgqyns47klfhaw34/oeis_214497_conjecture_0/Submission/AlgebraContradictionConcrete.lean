import FormalConjectures.Util.ProblemImports

example : False := by
  first
  | exact false_of_nontrivial_of_product_domain (ZMod 2) (ZMod 2)
  | exact false_of_nontrivial_of_product_domain ℕ ℕ
  | exact false_of_nontrivial_of_product_domain ℤ ℤ
  | exact false_of_nontrivial_of_product_domain ℚ ℚ
  | exact false_of_nontrivial_of_product_domain (ZMod 0) (ZMod 0)
  | exact CharP.false_of_nontrivial_of_char_one (R := ℕ)
  | exact CharP.false_of_nontrivial_of_char_one (R := ℤ)
  | exact CharP.false_of_nontrivial_of_char_one (R := ℚ)
  | exact CharP.false_of_nontrivial_of_char_one (R := ZMod 2)
  | exact CharP.false_of_nontrivial_of_char_one (R := ZMod 3)

-- separate synth checks
#synth IsDomain (ZMod 2 × ZMod 2)
#synth IsDomain (ℕ × ℕ)
#synth CharP ℕ 1
#synth CharP (ZMod 2) 1
