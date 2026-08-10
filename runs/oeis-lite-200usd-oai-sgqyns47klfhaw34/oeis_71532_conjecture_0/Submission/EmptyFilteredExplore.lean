import FormalConjectures.Util.ProblemImports
open CategoryTheory

instance : Category Empty where
  Hom X Y := PEmpty
  id X := nomatch X
  comp f g := nomatch f

#check CategoryTheory.IsFiltered.nonempty
#synth CategoryTheory.IsFiltered Empty

example : Nonempty Empty := CategoryTheory.IsFiltered.nonempty (J := Empty)
example : False := nomatch (Classical.choice (CategoryTheory.IsFiltered.nonempty (J := Empty)))
#print axioms _example
