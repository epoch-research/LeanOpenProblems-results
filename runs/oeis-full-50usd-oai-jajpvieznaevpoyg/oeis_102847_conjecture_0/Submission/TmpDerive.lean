import FormalConjectures.Util.ProblemImports

inductive E : Type deriving Nonempty
example : E := Classical.choice inferInstance
