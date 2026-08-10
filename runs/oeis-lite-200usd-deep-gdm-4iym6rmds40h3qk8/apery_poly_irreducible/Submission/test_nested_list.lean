import FormalConjectures.Util.ProblemImports

inductive T : Type
| mk : List (T → Empty) → T
