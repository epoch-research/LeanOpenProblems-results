import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| intro : (Bad -> False) -> Bad
