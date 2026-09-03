import Submission.UnrestrictedMomentCoefficientGap

/-! Type checks and permitted-axiom audit for the unrestricted comparison. -/

open Nat Filter
namespace Erdos821
open AnalyticSieve HigherDivisors

example (w A m : ℕ) (hw : 1 ≤ w) :
    (logMomentScale m : ℝ)^(w*(A+8)) /
      (Real.log (nearMomentX w A m : ℝ))^w <
        (1/2 : ℝ)^(w+1)/((w+1).factorial : ℝ) :=
  nearMoment_raw_coefficient_gap_unrestricted w A m hw

#print axioms factorial_succ_le_two_pow_mul_self_pow
#print axioms half_factorial_lt_order_power
#print axioms log_nearMomentX_ge_order_scale
#print axioms nearMoment_raw_coefficient_gap_unrestricted

end Erdos821
