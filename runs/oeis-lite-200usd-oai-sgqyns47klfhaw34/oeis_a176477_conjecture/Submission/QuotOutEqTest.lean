import FormalConjectures.Util.ProblemImports
#check Quot.out
#check Quot.out_eq
#check Quot.out_eq'
#check Quot.exists_rep
#check Quot.mk_out
example : (0:Nat) = 1 := by
  have hq : (Quot.mk (fun (_ _ : Nat) => True) 0) = (Quot.mk (fun (_ _ : Nat) => True) 1) := Quot.sound trivial
  have ho := congrArg Quot.out hq
  -- trace_state
  simpa using ho
#print axioms QuotOutEqTest._example
