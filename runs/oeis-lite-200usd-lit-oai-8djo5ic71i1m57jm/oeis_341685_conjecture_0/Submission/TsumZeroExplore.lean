import FormalConjectures.Util.ProblemImports
open Nat BigOperators Filter Topology Algebra
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

#check tsum_eq_zero_of_not_summable
#check summable_of_norm_bounded_eventually_geometric
#check NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
#check tendsto_zero_iff_norm_tendsto_zero
#check NormedAddCommGroup.tendsto_nhds_zero
#check Padic.norm_eq_zpow_neg_valuation
#check Padic.valuation
#check padicValNat_factorial_le
#check padicValNat_factorial_lt_of_ne_zero
#check sub_one_mul_padicValNat_factorial
#check Padic.norm_rat
#check padicNorm
#check padicNormE

example : IsAlgebraic ℚ (0 : Padic 3) := isAlgebraic_zero
example (h : xi_3_local = 0) : IsAlgebraic ℚ xi_3_local := by rw [h]; exact isAlgebraic_zero

example : xi_3_local = 0 := by
  unfold xi_3_local
  apply tsum_eq_zero_of_not_summable
  -- try prove not summable (should fail)
  intro hs
  have ht := hs.tendsto_atTop_zero
  -- terms tend to 0 actually
  sorry
