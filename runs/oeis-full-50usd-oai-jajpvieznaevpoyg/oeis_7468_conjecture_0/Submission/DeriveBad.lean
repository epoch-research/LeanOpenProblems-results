import FormalConjectures.Util.ProblemImports

inductive Bad : Prop where
| mk : Bad → Bad
  deriving Nonempty

theorem bad : False := by
  have hb : Bad := Classical.choice (inferInstance : Nonempty Bad)
  induction hb
#print axioms Bad.instNonempty
#print axioms bad
