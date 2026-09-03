import Submission.ResidueEquidistributionExplore
/-! API checks for a Tauberian transfer. -/
open Filter MeasureTheory
open scoped Topology
#check ContinuousOn.comp_continuous
#check Polynomial.eval_eq_sum_range
#check Polynomial.toContinuousMapOn_apply
#check ContinuousMap.norm_coe_le_norm
#check ContinuousMap.norm_apply_le_norm
#check ContinuousMap.norm_le
#check ContinuousMap.norm_le_iff
#check MeasureTheory.Integrable.mono'
#check norm_integral_le_of_norm_le
#check integral_gaussian
#check integral_add
#check integral_finset_sum
#check ContinuousMap.sub_apply
#check Summable.tsum_finsetSum
#check tsum_finsetSum
#check Summable.of_norm_bounded
#check norm_tsum_le_tsum_norm
#check Real.sqrt_div
#check Real.sqrt_mul
#check Real.exp_nat_mul
#check Real.exp_mul_nat
#check Polynomial.induction_on'
#check Polynomial.sum_monomial_eq
#check tendsto_finset_sum
#check Real.tendsto_one_add_div_pow_exp
