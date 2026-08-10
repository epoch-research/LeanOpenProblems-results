import FormalConjectures.Util.ProblemImports

macro "#print" "axioms" id:ident : command =>
  `(run_cmd Lean.logInfo "Hello!")

#print axioms Nat
