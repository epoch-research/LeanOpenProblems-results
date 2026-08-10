import FormalConjectures.Util.ProblemImports

inductive Bad : Prop
| mk : (Bad → False) → Bad
