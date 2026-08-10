import FormalConjectures.Util.ProblemImports
#check proof_irrel_heq
#check proof_irrel
#check HEq.ndrec
#check congrArg
#check congrFun
#check hcongr

example {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  exact proof_irrel_heq p q

example {P Q : ℤ → Prop} (hp : ∃ x, P x) (hq : ∃ x, Q x) : HEq (Classical.choose hp) (Classical.choose hq) := by
  have hh : HEq hp hq := proof_irrel_heq hp hq
  -- can we hcongr choose?
  fail_if_success exact hcongr (@Classical.choose) hh
  fail_if_success exact congrArg Classical.choose (by exact ?_)
  sorry
