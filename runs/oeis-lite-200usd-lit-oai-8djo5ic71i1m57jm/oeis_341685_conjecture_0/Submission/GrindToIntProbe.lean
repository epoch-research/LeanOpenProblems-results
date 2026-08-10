import FormalConjectures.Util.ProblemImports

#check Lean.Grind.toInt_uint64
#check Lean.Grind.toInt_uint16
#print Lean.Grind.toInt_uint64
#print axioms Lean.Grind.toInt_uint64

example : (UInt64.size - 1 : UInt64) = ((UInt64.size - 1 : UInt64).toNat) := by
  exact Lean.Grind.toInt_uint64 _

example : False := by
  have h := Lean.Grind.toInt_uint64 (UInt64.ofNat 0)
  -- inspect
  fail_if_success exact h
  trivial
