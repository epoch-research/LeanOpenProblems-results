import FormalConjectures.Util.ProblemImports

open CategoryTheory

-- Try to inhabit impossible homs in simple categories.
example : False := by
  exact CategoryTheory.hom_inl_inr_false (Type) (Type) (default)

example : False := by
  exact CategoryTheory.hom_inr_inl_false (Type) (Type) (default)

example : False := by
  exact CategoryTheory.WithInitial.false_of_to_star' (C := Type) (X := PUnit) default

example : False := by
  exact CategoryTheory.WithTerminal.false_of_from_star' (C := Type) (X := PUnit) default
