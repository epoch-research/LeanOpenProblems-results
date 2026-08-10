import FormalConjectures.Util.ProblemImports

theorem test_choice (P : Prop) : P :=
  Classical.choice (answer(sorry) : Nonempty P)

#print axioms test_choice
