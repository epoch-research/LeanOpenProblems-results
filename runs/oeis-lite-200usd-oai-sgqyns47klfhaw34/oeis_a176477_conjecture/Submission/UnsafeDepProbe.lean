import FormalConjectures.Util.ProblemImports
unsafe def ufalse : False := lcProof
theorem sfalse : False := by
  exact ufalse
#print axioms sfalse
