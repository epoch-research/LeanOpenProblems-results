import FormalConjectures.Util.ProblemImports

-- Product domains
example : False := by exact false_of_nontrivial_of_product_domain (ZMod 2) (ZMod 2)
example : False := by exact false_of_nontrivial_of_product_domain ℕ ℕ
example : False := by exact false_of_nontrivial_of_product_domain ℤ ℤ
example : False := by exact false_of_nontrivial_of_product_domain ℚ ℚ
example : False := by exact false_of_nontrivial_of_product_domain (ULift (ZMod 2)) (ULift (ZMod 2))

-- Characteristic one contradictions
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := ZMod 0)
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := ULift (ZMod 1))
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := PUnit)
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := Unit)

-- topological contradictions
example : False := by exact not_preirreducible_nontrivial_t2 Bool
example : False := by exact not_preirreducible_nontrivial_t2 Prop
example : False := by exact not_preirreducible_nontrivial_t2 (ULift Bool)
example : False := by exact not_preirreducible_nontrivial_t2 (Fin 2)
