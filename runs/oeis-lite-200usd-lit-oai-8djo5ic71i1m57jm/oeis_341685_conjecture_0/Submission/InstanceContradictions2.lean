import FormalConjectures.Util.ProblemImports

-- topological contradiction candidates
#synth PreirreducibleSpace ℝ
#synth T2Space ℝ
#synth Nontrivial ℝ
example : False := by
  exact not_preirreducible_nontrivial_t2 ℝ

#synth PreirreducibleSpace (Padic 3)
#synth T2Space (Padic 3)
#synth Nontrivial (Padic 3)
example [Fact (Nat.Prime 3)] : False := by
  exact not_preirreducible_nontrivial_t2 (Padic 3)

-- char one contradiction candidates
#synth CharP ℕ 1
example : False := by exact CharP.false_of_nontrivial_of_char_one (R:=ℕ)
