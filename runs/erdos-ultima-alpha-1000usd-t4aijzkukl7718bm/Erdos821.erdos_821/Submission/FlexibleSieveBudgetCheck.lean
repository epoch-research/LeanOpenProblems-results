import Submission.FlexibleSieveBudget

/-! Exact-type checks and axiom audit for the flexible method budget. -/

#print axioms Erdos821.chebyshevRatioConstant_lt_decimal
#print axioms Erdos821.FlexibleRetentionBudget
#print axioms Erdos821.FlexibleRetentionBudget.cofactor_le
#print axioms Erdos821.FlexibleRetentionBudget.modulus_level_required
#print axioms Erdos821.FlexibleRetentionBudget.cube_root_requires_large_modulus
#print axioms Erdos821.FlexibleRetentionBudget.below_half_cutoff
#print axioms Erdos821.flexible_chebyshev_parameters_retention_budget
#print axioms Erdos821.flexible_chebyshev_parameters_exponent_bound
#print axioms Erdos821.FlexibleRetentionBudget.modulus_level_tends_to_one

open Erdos821 Erdos821.AnalyticSieve in
example (r t b h : ℕ) (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8192/675 : ℝ)*(t : ℝ)*h < chebyshevRatioConstant*((b : ℝ)-1)^2) :
    1-(b : ℝ)/t < (51767/100000 : ℝ) :=
  flexible_chebyshev_parameters_exponent_bound r t b h heq hrt hb hc

open Erdos821 in
example (δ β κ j : ℝ) (h : FlexibleRetentionBudget δ β κ j) (hβ : β ≤ 1/3) :
    (6470683/9830400 : ℝ) ≤ δ :=
  h.cube_root_requires_large_modulus hβ
