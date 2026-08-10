import FormalConjectures.Util.ProblemImports

inductive MyProp : Prop where
  | mk : MyProp

instance : Nonempty MyProp := ⟨MyProp.mk⟩

partial def get_myProp (u : Unit) : MyProp :=
  get_myProp u

theorem test_theorem : MyProp :=
  get_myProp ()

#print axioms test_theorem

