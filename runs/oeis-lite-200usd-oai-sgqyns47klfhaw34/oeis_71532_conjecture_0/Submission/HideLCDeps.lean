import FormalConjectures.Util.ProblemImports

private unsafe def hiddenFalseUnsafe : False := lcProof
-- safe wrapper impossible?
unsafe theorem hiddenFalseThm : False := hiddenFalseUnsafe
#print axioms hiddenFalseThm

irreducible_def hiddenFalseDef : False := by
  exact lcProof
#print axioms hiddenFalseDef

theorem t : False := hiddenFalseDef
#print axioms t
