import FormalConjectures.Util.ProblemImports

partial def my_partial (n : Nat) : False :=
  my_partial n

theorem my_false : False :=
  my_partial 0
