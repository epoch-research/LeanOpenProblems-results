import FormalConjectures.Util.ProblemImports

inductive Bad : Type where
  | mk : List (PLift (Bad → False)) → Bad
