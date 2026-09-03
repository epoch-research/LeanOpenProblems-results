import Submission.SubexponentialEulerCost

/-! Type and axiom audit. -/

open Erdos821.HigherDivisors

#check logEulerCost_summable
#check logEulerCost_nonneg
#check eulerCost_pos
#check eulerCost_ge_one
#check finite_euler_product_le
#check tendsto_log_affine_nat_div
#check tendsto_logEulerCost_div
#check eventually_eulerCost_le_exp
#check harmonicMoment_totient_ratio_le_cost
#print axioms logEulerCost_summable
#print axioms logEulerCost_nonneg
#print axioms eulerCost_pos
#print axioms eulerCost_ge_one
#print axioms finite_euler_product_le
#print axioms tendsto_log_affine_nat_div
#print axioms tendsto_logEulerCost_div
#print axioms eventually_eulerCost_le_exp
#print axioms harmonicMoment_totient_ratio_le_cost
