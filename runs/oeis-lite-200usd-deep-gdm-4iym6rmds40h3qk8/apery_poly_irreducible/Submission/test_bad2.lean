import FormalConjectures.Util.ProblemImports

inductive T (F : Type → Type) : Type
| mk : (F (T F) → False) → T F
