import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| mk : (Bad → False) → Bad
