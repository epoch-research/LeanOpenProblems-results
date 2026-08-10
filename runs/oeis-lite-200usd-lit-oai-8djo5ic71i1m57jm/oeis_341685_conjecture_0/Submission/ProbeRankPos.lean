import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#check Module.rank_pos
#check Module.rank_pos_iff
#check Module.rank_eq_zero_iff
#check Module.rank_zero_iff
#check Module.rank_eq_zero
#check Cardinal.mk_ne_zero

example : 0 < Module.rank ℚ (Padic 3) := by
  apply?
example : Module.rank ℚ (Padic 3) ≠ 0 := by
  apply?
