import FormalConjectures.Util.ProblemImports

#print Equiv.propEquivBool
#check Equiv.propEquivBool
#print axioms Equiv.propEquivBool
#check Equiv.propEquivBool.toFun
#check Equiv.propEquivBool.invFun

example (P : Prop) : Bool := Equiv.propEquivBool P
example (b : Bool) : Prop := Equiv.propEquivBool.symm b

example (P : Prop) : P := by
  let b := Equiv.propEquivBool P
  -- what can be extracted?
  have h := (Equiv.propEquivBool.symm_apply_apply P)
  exact?
