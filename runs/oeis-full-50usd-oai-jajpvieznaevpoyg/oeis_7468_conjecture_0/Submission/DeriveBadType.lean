import FormalConjectures.Util.ProblemImports

inductive Bad : Type where
| mk : Bad → Bad
  deriving Inhabited

theorem bad : False := by
  let b : Bad := default
  induction b
#print axioms Bad.instInhabited
#print axioms bad
