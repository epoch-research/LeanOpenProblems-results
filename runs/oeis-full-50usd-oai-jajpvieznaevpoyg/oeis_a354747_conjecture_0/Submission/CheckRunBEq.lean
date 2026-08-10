import FormalConjectures.Util.ProblemImports
structure Elt where u : Nat; v : Nat deriving BEq, DecidableEq
structure RunState where
  base : Elt
  a1 : Elt
  deriving BEq, DecidableEq
#print instBEqRunState
#print instBEqRunState.beq
