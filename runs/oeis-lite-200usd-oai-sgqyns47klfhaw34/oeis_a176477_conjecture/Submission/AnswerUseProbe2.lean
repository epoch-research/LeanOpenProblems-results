import FormalConjectures.Util.ProblemImports
set_option google.answer "alwaysTrue"
example : False := by
  change answer(sorry)
  trivial
example (P : Prop) : P := by
  exact (show answer(sorry) from trivial)
example (P : Prop) : P := by
  change (answer(sorry) : Prop)
  trivial
