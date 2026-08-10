import FormalConjectures.Util.ProblemImports

instance badInhFalse : Inhabited False where
  default := badInhFalse.default

theorem bad : False := default
#print axioms bad
