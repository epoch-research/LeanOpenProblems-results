import FormalConjectures.Util.ProblemImports

open CategoryTheory

example : False := by
  exact CategoryTheory.hom_inl_inr_false (Discrete PUnit) (Discrete PUnit) (default)

example : False := by
  exact CategoryTheory.hom_inr_inl_false (Discrete PUnit) (Discrete PUnit) (default)

example : False := by
  exact CategoryTheory.WithTerminal.false_of_from_star (C := Discrete PUnit) (X := ⟨()⟩) default

example : False := by
  exact CategoryTheory.WithInitial.false_of_to_star (C := Discrete PUnit) (X := ⟨()⟩) default
