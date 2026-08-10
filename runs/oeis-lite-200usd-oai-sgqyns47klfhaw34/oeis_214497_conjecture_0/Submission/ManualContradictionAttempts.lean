import FormalConjectures.Util.ProblemImports

example : False := by
  exact false_of_nontrivial_of_subsingleton PUnit

example : False := by
  exact not_finite Unit

example : False := by
  exact not_finite (Fin 1)

example : False := by
  exact false_of_nontrivial_of_subsingleton True

example : False := by
  exact false_of_nontrivial_of_subsingleton False
