import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Countable (Padic 3)
#synth Encodable (Padic 3)
#synth Nonempty (Padic 3)
#synth Infinite (Padic 3)
#check Padic.infinite
#check Padic.uncountable
#check not_countable_real
#check uncountable_iff
#check Cardinal.mk_padic
#check Cardinal.mk_real
#check Padic.equiv
example : False := by
  haveI : Countable (Padic 3) := inferInstance
  exact not_countable_iff.mpr ?_
