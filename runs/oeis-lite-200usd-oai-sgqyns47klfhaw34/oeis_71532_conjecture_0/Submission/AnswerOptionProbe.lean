import FormalConjectures.Util.ProblemImports
set_option google.answer always_true
-- answer(sorry) as a proposition expression defaults to True only when expected type is Prop itself.
#check (answer(sorry) : Prop)
example : (answer(sorry) : Prop) := by trivial
#print axioms AnswerOptionProbe._example_1
-- But not as proof of arbitrary proposition
example : False := by
  change (answer(sorry) : Prop)
  trivial
