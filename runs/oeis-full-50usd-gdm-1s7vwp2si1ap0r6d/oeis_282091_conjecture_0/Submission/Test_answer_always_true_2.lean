import FormalConjectures.Util.ProblemImports

set_option google.answer "always_true"

def MyProp : Prop :=
  answer(sorry)

theorem my_theorem : MyProp :=
  True.intro

#print axioms my_theorem
