import FormalConjectures.Util.ProblemImports

set_option google.answer "always_true"

def MyProp : Prop := False

theorem my_theorem : MyProp :=
  answer(sorry)

#print axioms my_theorem
