import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
open Filter Topology

#check Filter.Tendsto
#check NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
#check tendsto_iff_norm_tendsto_zero
#check Metric.tendsto_nhds
#check Padic.valuation
#check Padic.nnnorm_eq_zpow_neg_valuation
#check Padic.norm_eq_zpow_neg_valuation
#check padicValNat_factorial
#check padicNormE

example : Filter.Tendsto (fun k : ℕ => (Nat.factorial k : Padic 3)) Filter.atTop (𝓝 0) := by
  simp? -- see if term convergence exists

example : Summable (fun k : ℕ => (Nat.factorial k : Padic 3)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  -- cofinite follows from atTop for Nat if terms tend to zero
  filter_mono atTop_le_cofinite
  exact (show Filter.Tendsto (fun k : ℕ => (Nat.factorial k : Padic 3)) Filter.atTop (𝓝 0) from by
    simp?)
