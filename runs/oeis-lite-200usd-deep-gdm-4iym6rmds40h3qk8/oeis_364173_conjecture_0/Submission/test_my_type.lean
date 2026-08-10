import FormalConjectures.Util.ProblemImports

set_option google.answer "with_auxiliary"

def my_type : Prop := True

theorem foo : my_type := answer(sorry)

#print axioms foo
