import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check tsum_eq_zero_of_not_summable
#check tsum_eq_zero
#check Summable.tsum_eq_zero
#check hasSum_iff_tendsto_nat
#check Padic.tendsto_pow_padicNorm_nhds_zero
#check padicValNat_factorial

example : xi_3_local = 0 := by
  unfold xi_3_local
  simp

example : ¬ Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  simp
