import FormalConjectures.Util.ProblemImports

-- Try direct metavariable/typeclass inference.
example : False := by
  exact CharP.false_of_nontrivial_of_char_one

example : False := by
  exact false_of_nontrivial_of_product_domain _ _

example : False := by
  exact not_preirreducible_nontrivial_t2 _

example : False := by
  exact false_of_nontrivial_of_subsingleton _

example : False := by
  exact not_finite _

example : False := by
  exact Fintype.false
