import FormalConjectures.Util.ProblemImports
set_option pp.all true

example (h0 : ∃ z : ℤ, z = 0) (h1 : ∃ z : ℤ, z = 1) :
    HEq h0 h1 := proof_irrel_heq h0 h1

#check congrArg
#check congrFun
#check HEq.ndrec
#check heq_of_eq
#check eq_of_heq
#check congr_heq
#check hcongr

example (h0 : ∃ z : ℤ, z = 0) (h1 : ∃ z : ℤ, z = 1) :
    HEq (Classical.choose h0) (Classical.choose h1) := by
  have hh : HEq h0 h1 := proof_irrel_heq h0 h1
  -- suggestions
  apply?

example (h0 : ∃ z : ℤ, z = 0) (h1 : ∃ z : ℤ, z = 1) :
    Classical.choose h0 = Classical.choose h1 := by
  have hh : HEq h0 h1 := proof_irrel_heq h0 h1
  have hc : HEq (Classical.choose h0) (Classical.choose h1) := by
    apply?
  exact eq_of_heq hc
