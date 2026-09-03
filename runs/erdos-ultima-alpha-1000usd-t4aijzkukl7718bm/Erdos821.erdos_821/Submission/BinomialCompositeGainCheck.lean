import Submission.BinomialCompositeGain

/-! Type and axiom audit for the binomial improvement of the fixed exponent. -/
open Nat Filter
namespace Erdos821
example (γ : ℝ)
    (hγ : γ < 1/2 + 1/(2400000*Sieve.totientRatioAverageConstant+10)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_g_gt_binomial_composite_uniform γ hγ
example (ε : ℝ)
    (hε : 1/2 - 1/(2400000*Sieve.totientRatioAverageConstant+10) < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_binomial_composite_range ε hε
#check @eventually_progression_mangoldt_five_eighths
#print axioms eventually_progression_mangoldt_five_eighths
#check @eventually_product_mangoldt_weight_nine_sixteenths
#print axioms eventually_product_mangoldt_weight_nine_sixteenths
#check @binomial_structured_parameter_large
#print axioms binomial_structured_parameter_large
#check @binomial_structured_coefficient_bound
#print axioms binomial_structured_coefficient_bound
#check @binomial_structured_sieve_main_small
#print axioms binomial_structured_sieve_main_small
#check @binomial_smooth_structured_weight_retained
#print axioms binomial_smooth_structured_weight_retained
#check @eventually_binomial_structured_retained_weight
#print axioms eventually_binomial_structured_retained_weight
#check @eventually_binomial_structured_prime_count
#print axioms eventually_binomial_structured_prime_count
#check @eventually_binomial_structured_smooth_family
#print axioms eventually_binomial_structured_smooth_family
#check @infinite_g_gt_binomial_composite_limit
#print axioms infinite_g_gt_binomial_composite_limit
#check @infinite_g_gt_binomial_composite_uniform
#print axioms infinite_g_gt_binomial_composite_uniform
#check @erdos_821_binomial_composite_range
#print axioms erdos_821_binomial_composite_range
#check @binomial_composite_gain_gt_thirty_three_old_gain
#print axioms binomial_composite_gain_gt_thirty_three_old_gain
end Erdos821
