import FormalConjectures.Util.ProblemImports

inductive E : Type where
deriving instance Nonempty for E

noncomputable example : E := Classical.choice (inferInstance : Nonempty E)
#print axioms E.instNonempty
