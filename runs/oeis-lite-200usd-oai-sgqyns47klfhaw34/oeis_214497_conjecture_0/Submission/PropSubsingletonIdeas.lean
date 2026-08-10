import FormalConjectures.Util.ProblemImports

#check proof_irrel_heq
#check Subsingleton.elim
#check HEq
#check Eq.ndrec
#check cast

example (P : Prop) : P := by
  have hheq : HEq True.intro (show P from by sorry) := proof_irrel_heq _ _
  sorry

example (P : Prop) : P := by
  fail_if_success exact cast (Subsingleton.elim True P) True.intro
  sorry
