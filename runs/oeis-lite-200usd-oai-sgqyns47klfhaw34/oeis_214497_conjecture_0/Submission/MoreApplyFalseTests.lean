import FormalConjectures.Util.ProblemImports

#check false_of_nontrivial_of_product_domain
#check neZero_zero_iff_false
#check CategoryTheory.hom_inl_inr_false
#check CategoryTheory.hom_inr_inl_false

example : False := by
  first
  | exact neZero_zero_iff_false.mp inferInstance
  | exact false_of_nontrivial_of_product_domain PUnit PUnit
  | exact false_of_nontrivial_of_product_domain Empty PUnit
