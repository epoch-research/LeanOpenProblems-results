import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#print tsum
#check tsum_eq_zero_of_not_summable
#check HasSum.tsum_eq
#check summable_of_norm_bounded_eventually
#check Padic.summable_of_forall_norm_tendsto_zero
example : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  apply?
