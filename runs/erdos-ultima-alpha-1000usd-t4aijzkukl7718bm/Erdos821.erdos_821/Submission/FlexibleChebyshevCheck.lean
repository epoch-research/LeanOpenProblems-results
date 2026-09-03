import Submission.FlexibleChebyshevSpecialization

/-! Exact-type checks and permitted-axiom audit for flexible Chebyshev gains. -/

#print axioms Erdos821.eventually_mangoldt_lower_constant
#print axioms Erdos821.eventually_progression_mangoldt_lower_constant
#print axioms Erdos821.eventually_product_mangoldt_lower_constant
#print axioms Erdos821.eventually_independent_total_error_divisor
#print axioms Erdos821.flexibleStructuredCountConstant
#print axioms Erdos821.flexible_independent_count_of_weight
#print axioms Erdos821.independentMainLimit
#print axioms Erdos821.independentMainRemainder
#print axioms Erdos821.independent_sieve_main_limit_upper
#print axioms Erdos821.eventually_independent_sieve_main_constant
#print axioms Erdos821.flexible_smooth_weight_retained
#print axioms Erdos821.eventually_flexible_chebyshev_retained_weight
#print axioms Erdos821.eventually_flexible_chebyshev_smooth_family
#print axioms Erdos821.infinite_g_gt_flexible_chebyshev_parameters
#print axioms Erdos821.chebyshevRatioConstant_gt_decimal
#print axioms Erdos821.infinite_g_gt_flexible_chebyshev_uniform
#print axioms Erdos821.infinite_g_gt_point_five_one_seven_six_six
#print axioms Erdos821.erdos_821_flexible_chebyshev_range
#print axioms Erdos821.erdos_821_point_four_eight_two_three_four
#print axioms Erdos821.flexible_chebyshev_strict_improvement

open Erdos821 in
example (γ : ℝ) (hγ : γ < 2070643/4000001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_g_gt_flexible_chebyshev_uniform γ hγ

open Erdos821 in
example (ε : ℝ) (hε : 1929358/4000001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_flexible_chebyshev_range ε hε

open Erdos821 Erdos821.AnalyticSieve in
example (r t b h : ℕ) (heq : r+b+h=t) (hrt : 2*r+1 ≤ t)
    (hb : 2 ≤ b) (hh : 1 ≤ h) (hcap : t+5 ≤ 5*b)
    (hc : (8192/675 : ℝ)*(t : ℝ)*h < chebyshevRatioConstant*((b : ℝ)-1)^2)
    (γ : ℝ) (hγ : γ < 1-(b : ℝ)/t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_g_gt_flexible_chebyshev_parameters r t b h heq hrt hb hh hcap hc γ hγ
