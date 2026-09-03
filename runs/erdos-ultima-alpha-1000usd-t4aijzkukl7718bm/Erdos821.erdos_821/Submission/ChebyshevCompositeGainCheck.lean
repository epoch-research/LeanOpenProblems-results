import Submission.ChebyshevCompositeGain

/-! Exact-type and axiom checks for the stronger arithmetic lower bound. -/

#print axioms Erdos821.AnalyticSieve.chebyshev_floor_kernel_le_one
#print axioms Erdos821.AnalyticSieve.log_factorial_eq_mangoldt_floor_sum
#print axioms Erdos821.AnalyticSieve.chebyshev_factorial_ratio_le_mangoldt
#print axioms Erdos821.AnalyticSieve.nine_tenths_lt_chebyshevRatioConstant
#print axioms Erdos821.AnalyticSieve.tendsto_log_factorial_multiple_residual
#print axioms Erdos821.AnalyticSieve.tendsto_chebyshevFactorialRatio_div
#print axioms Erdos821.AnalyticSieve.eventually_mangoldt_nine_tenths
#print axioms Erdos821.eventually_product_mangoldt_weight_seven_eighths
#print axioms Erdos821.chebyshev_independent_sieve_main_small
#print axioms Erdos821.chebyshev_independent_smooth_weight_retained
#print axioms Erdos821.eventually_chebyshev_independent_retained_weight
#print axioms Erdos821.eventually_chebyshev_independent_smooth_family
#print axioms Erdos821.infinite_g_gt_chebyshev_parameters
#print axioms Erdos821.infinite_g_gt_chebyshev_uniform
#print axioms Erdos821.erdos_821_chebyshev_range
#print axioms Erdos821.erdos_821_chebyshev_point_four_eight_five

open Erdos821 in
example (γ : ℝ) (hγ : γ < 2064/4001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_g_gt_chebyshev_uniform γ hγ

open Erdos821 in
example (ε : ℝ) (hε : 1937/4001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_chebyshev_range ε hε
