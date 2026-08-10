import FormalConjectures.Util.ProblemImports
#check Lean.reduceNat
#check Lean.reduceBool
example : Lean.reduceNat 0 = 0 := rfl
example : Lean.reduceNat 1 = 1 := rfl
example : Lean.reduceNat 2 = 2 := rfl
example : Lean.reduceBool false = false := rfl
example : Lean.reduceBool true = true := rfl
-- this would need false equality, should fail
-- example : (0:Nat)=1 := Lean.ofReduceNat 0 1 (by rfl)
#print axioms Lean.ofReduceNat
#print axioms Lean.ofReduceBool
