import FormalConjectures.Util.ProblemImports

inductive Bad : Type where
| mk : (Bad → Bad) → Bad
