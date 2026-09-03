import Submission.IndependentCompositeBarrier

/-! Exact-type checks and axiom audit for the independent-parameter refinement. -/

#print axioms Erdos821.independent_sieve_error_pow_bound
#print axioms Erdos821.eventually_independent_total_error_small
#print axioms Erdos821.independent_sieve_main_small
#print axioms Erdos821.independent_coefficient_cap
#print axioms Erdos821.independent_rough_count_le
#print axioms Erdos821.eventually_independent_smooth_family
#print axioms Erdos821.infinite_g_gt_independent_parameters
#print axioms Erdos821.infinite_g_gt_independent_uniform
#print axioms Erdos821.erdos_821_independent_range
#print axioms Erdos821.erdos_821_independent_point_four_nine

example (γ : ℝ) (hγ : γ < 2041/4001) :
    {n : ℕ | (Erdos821.g n : ℝ) > (n : ℝ)^γ}.Infinite :=
  Erdos821.infinite_g_gt_independent_uniform γ hγ

#print axioms Erdos821.independent_parameters_cutoff_bound
#print axioms Erdos821.independent_parameters_exponent_bound
