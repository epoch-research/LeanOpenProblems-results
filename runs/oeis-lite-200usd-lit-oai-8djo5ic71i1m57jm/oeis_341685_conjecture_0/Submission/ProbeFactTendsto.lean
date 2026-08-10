import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#check NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
#check tendsto_nhds_zero_iff_norm_tendsto_zero
#check padicNorm
#check padicNorm_factorial
#check padicValRat_factorial
#check padicValNat_factorial
#check Nat.factorial

example : Tendsto (fun k : ℕ => (Nat.factorial k : Padic 3)) atTop (𝓝 0) := by
  apply?

example : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply?
