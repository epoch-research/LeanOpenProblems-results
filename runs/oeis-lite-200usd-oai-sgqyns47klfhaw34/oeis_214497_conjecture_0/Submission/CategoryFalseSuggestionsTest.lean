import FormalConjectures.Util.ProblemImports
open CategoryTheory

#check CategoryTheory.Join.false_of_right_to_left
#check CategoryTheory.WithTerminal.false_of_from_star
#check CategoryTheory.WithInitial.false_of_to_star

example : False := by
  exact CategoryTheory.Join.false_of_right_to_left (C := Type) (D := Type) (𝟙 (CategoryTheory.Join.right PUnit))

example : False := by
  exact CategoryTheory.WithTerminal.false_of_from_star (C := Type) (𝟙 CategoryTheory.WithTerminal.star)

example : False := by
  exact CategoryTheory.WithInitial.false_of_to_star (C := Type) (𝟙 CategoryTheory.WithInitial.star)
