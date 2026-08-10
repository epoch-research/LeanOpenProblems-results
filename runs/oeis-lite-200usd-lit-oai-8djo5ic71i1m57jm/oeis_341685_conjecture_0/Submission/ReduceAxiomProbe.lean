import FormalConjectures.Util.ProblemImports
#check Lean.reduceNat
#check Lean.reduceBool
example : Lean.reduceNat 0 = 0 := rfl
-- should fail:
-- example : Lean.reduceNat 0 = 1 := rfl
-- example : Lean.reduceBool false = true := rfl
example : 0 = 0 := Lean.ofReduceNat 0 0 rfl
example : false = false := Lean.ofReduceBool false false rfl
#print axioms Lean.reduceNat
#print axioms Lean.reduceBool
