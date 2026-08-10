import FormalConjectures.Util.ProblemImports

structure SProp (P : Prop) where
  out : P
  deriving Nonempty

theorem arbitrary (P : Prop) : P := (Classical.choice (inferInstance : Nonempty (SProp P))).out
#print axioms arbitrary
