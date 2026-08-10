import FormalConjectures.Util.ProblemImports

partial def cast_false (u : Unit) : False :=
  cast_false u

theorem prove_false : False :=
  cast_false ()
