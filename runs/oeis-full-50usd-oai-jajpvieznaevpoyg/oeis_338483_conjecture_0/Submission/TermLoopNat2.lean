import FormalConjectures.Util.ProblemImports

def badNat : Nat → Nat
| n => badNat n + 1
termination_by x => x
decreasing_by
  exact Nat.lt_irrefl _

example : badNat 0 = badNat 0 + 1 := by rfl

theorem badNatFalse : False := by
  have h : badNat 0 = badNat 0 + 1 := by rfl
  omega
#print axioms badNatFalse
