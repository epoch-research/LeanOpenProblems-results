import FormalConjectures.Util.ProblemImports

partial def test_unsafe_thm (_ : Unit) : False :=
  test_unsafe_thm ()

#print axioms test_unsafe_thm
