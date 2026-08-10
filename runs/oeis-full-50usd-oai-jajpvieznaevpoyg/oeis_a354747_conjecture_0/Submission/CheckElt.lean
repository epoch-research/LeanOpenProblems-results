import FormalConjectures.Util.ProblemImports
structure Elt where
  u : Nat
  v : Nat
  deriving BEq, DecidableEq
#print instBEqElt.beq
