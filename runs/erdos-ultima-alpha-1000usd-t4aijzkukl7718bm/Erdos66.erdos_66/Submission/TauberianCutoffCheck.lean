import Submission.TauberianTestsExplore
/-! Cutoff and measure API checks. -/
open Filter MeasureTheory
open scoped Topology
#check Real.volume_Icc
#check Real.volume_real_Icc
#check Real.volume_Icc_toReal
#check MeasureTheory.integrableOn_const
#check integrable_indicator_iff
#check integrableOn_Icc
#check MeasureTheory.integral_indicator_one
#check Set.indicator_nonneg
#check Set.indicator_le_self
#check Summable.sum_le_tsum
#check Summable.tsum_le_tsum
#check tsum_eq_sum
#check tsum_eq_sum' 
#check tendsto_order
#check Erdos66ResidueEquidistribution.witness_series_eventually_ne_zero
#check ContinuousMap.toContinuousMap_apply
#check Real.exp_neg
#check Real.exp_log
