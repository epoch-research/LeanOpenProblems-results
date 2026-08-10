import FormalConjectures.Util.ProblemImports
open CategoryTheory

#check CategoryTheory.hom_inr_inl_false
#check CategoryTheory.hom_inl_inr_false
#check CategoryTheory.Join.false_of_right_to_left
#check CategoryTheory.WithInitial.false_of_to_star
#check CategoryTheory.WithTerminal.false_of_from_star

-- Inspect hom types in sum/join/with initial terminal
#check (Sum.inr (PUnit.unit) : Sum PUnit PUnit)
#check (Sum.inl (PUnit.unit) : Sum PUnit PUnit)
#check (by infer_instance : Category (Sum PUnit PUnit))
#check (by infer_instance : Category PUnit)

example : False := by
  -- can we synthesize a morphism in sum category?
  let f : (Sum.inr PUnit.unit : Sum PUnit PUnit) ⟶ (Sum.inl PUnit.unit) := by
    infer_instance
  exact CategoryTheory.hom_inr_inl_false PUnit PUnit f

