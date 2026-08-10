import FormalConjectures.Util.ProblemImports

#check not_preirreducible_nontrivial_t2
#print axioms not_preirreducible_nontrivial_t2

example : False := by
  exact not_preirreducible_nontrivial_t2 (X := Bool)

example : False := by
  exact not_preirreducible_nontrivial_t2 (X := Prop)

example : False := by
  exact not_preirreducible_nontrivial_t2 (X := ℝ)

example : False := by
  exact not_preirreducible_nontrivial_t2 (X := Set ℕ)

example : False := by
  exact not_preirreducible_nontrivial_t2 (X := Fin 2)
