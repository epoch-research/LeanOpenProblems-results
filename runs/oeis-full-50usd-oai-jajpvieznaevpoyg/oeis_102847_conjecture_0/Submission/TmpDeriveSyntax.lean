import FormalConjectures.Util.ProblemImports

inductive E : Type where
| mk : E
deriving instance Nonempty for E

example : E := Classical.choice (inferInstance : Nonempty E)
