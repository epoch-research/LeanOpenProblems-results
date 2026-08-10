import FormalConjectures.Util.ProblemImports
open Google

theorem bad1 : False := by
  change answer(sorry)
  trivial

example : False := by
  show answer(sorry)
  trivial

#print axioms bad1
