import FormalConjectures.Util.ProblemImports
#synth IsDomain (ℕ × ℕ)
#synth CharP ℕ 1
#synth Nontrivial (ZMod 1)
#synth IsDomain (ZMod 2 × ZMod 2)
example : False := by
  -- exact false_of_nontrivial_of_product_domain ℕ ℕ
  fail_if_success exact false_of_nontrivial_of_product_domain ℕ ℕ
  fail_if_success exact CharP.false_of_nontrivial_of_char_one (R := ℕ)
  trivial
