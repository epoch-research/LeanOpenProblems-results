import FormalConjectures.Util.ProblemImports

instance instBad : Inhabited False where
  default := instBad.default

theorem circularFalse : False := default
#print axioms circularFalse
