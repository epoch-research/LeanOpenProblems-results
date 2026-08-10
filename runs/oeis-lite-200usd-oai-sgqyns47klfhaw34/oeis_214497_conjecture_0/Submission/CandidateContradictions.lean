import FormalConjectures.Util.ProblemImports

#print axioms false_of_nontrivial_of_subsingleton
#print axioms not_finite
#print axioms CategoryTheory.zero_not_simple
#print axioms CharP.false_of_nontrivial_of_char_one
#print axioms Finite.false
#print axioms Infinite.false

-- Try syntheses that would instantiate contradictions
#synth Nontrivial (Fin 1)
#synth Subsingleton (Fin 2)
#synth Infinite (Fin 1)
#synth Finite ℕ
#synth CharP ℕ 1
#synth Nontrivial PUnit
#synth Subsingleton Bool

example : False := by
  -- exact false_of_nontrivial_of_subsingleton (Fin 1)
  fail_if_success exact false_of_nontrivial_of_subsingleton (Fin 1)
  fail_if_success exact not_finite ℕ
  fail_if_success exact CharP.false_of_nontrivial_of_char_one (R := ℕ)
  exact? 
