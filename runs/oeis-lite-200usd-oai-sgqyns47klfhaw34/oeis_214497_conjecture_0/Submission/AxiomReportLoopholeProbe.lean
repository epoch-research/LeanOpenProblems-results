import FormalConjectures.Util.ProblemImports

unsafe def ufalse : False := by
  exact lcProof

-- Can a safe theorem call unsafe? expected no.
theorem safe_from_unsafe : False := by
  exact ufalse

#print axioms safe_from_unsafe

-- Existing dangerous constants axiom reports
#check lcProof
#print axioms lcProof
#check Lean.ofReduceBool
#print axioms Lean.ofReduceBool
