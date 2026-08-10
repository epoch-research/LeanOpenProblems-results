import FormalConjectures.Util.ProblemImports

-- Category zero_not_simple on trivial category?
example : False := by
  exact CategoryTheory.zero_not_simple (Discrete PUnit)

-- false_of_nontrivial_of_product_domain for existing product instances?
example : False := by
  exact false_of_nontrivial_of_product_domain (ZMod 2) (ZMod 2)

-- CharP contradiction?
example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := ZMod 2)
