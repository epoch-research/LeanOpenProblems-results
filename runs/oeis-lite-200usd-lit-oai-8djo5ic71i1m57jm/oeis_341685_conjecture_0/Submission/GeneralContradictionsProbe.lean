import FormalConjectures.Util.ProblemImports
#synth IsDomain (ℚ × ℚ)
#synth CharP ℚ 1
#synth Finite ℕ
#synth Fintype ℕ
#synth Subsingleton ℕ
#synth PreirreducibleSpace ℚ
#synth T2Space ℚ
#synth Nontrivial ℚ
example : False := by exact false_of_nontrivial_of_product_domain ℚ ℚ
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := ℚ)
example : False := by exact not_preirreducible_nontrivial_t2 ℚ
