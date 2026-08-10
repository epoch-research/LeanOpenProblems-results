import FormalConjectures.Util.ProblemImports

inductive E : Type where
  deriving Nonempty

noncomputable example : E := Classical.choice (inferInstance : Nonempty E)
