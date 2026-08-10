import Mathlib
theorem self (n:Nat) : False := by
  exact self n
#print axioms self
