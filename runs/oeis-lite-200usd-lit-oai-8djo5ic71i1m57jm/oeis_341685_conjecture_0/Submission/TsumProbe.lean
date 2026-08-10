import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
#check tsum_eq_zero_of_not_summable
#check Summable.tsum_eq
#check summable_of_norm_bounded_eventually
#check summable_of_tendsto_norm_zero
#check Padic.norm_padicNorm
#check Padic.norm_eq_zpow_neg_val
#check Padic.norm_intCast
#check Padic.norm_natCast
#check Padic.tendsto_pow_padicNorm_nhds_zero
#check IsAlgebraic.zero
#check isAlgebraic_algebraMap
#check IsAlgebraic.algebraMap
example : IsAlgebraic ℚ (0 : Padic 3) := by exact isAlgebraic_algebraMap
example : IsAlgebraic ℚ ((0 : ℚ) : Padic 3) := by exact isAlgebraic_algebraMap
-- try exact? for algebraic xi
example : IsAlgebraic ℚ (xi_3) := by
  unfold xi_3
  fail_if_success exact isAlgebraic_algebraMap
  sorry
