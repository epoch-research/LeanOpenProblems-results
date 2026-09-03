import Submission.NearMomentCoefficientGap

/-! Exact-type checks and permitted-axiom audit for coefficient comparisons. -/

open Nat Filter
namespace Erdos821
open AnalyticSieve HigherDivisors

example (w A m : ℕ) (hw : 1 ≤ w)
    (hR : nearMomentR w A m+1 ≤ logMomentScale m) :
    (logMomentScale m : ℝ)^(w*(A+8)) /
      (Real.log (nearMomentX w A m : ℝ))^w <
        (1/2 : ℝ)^(w+1)/((w+1).factorial : ℝ) :=
  nearMoment_raw_coefficient_gap w A m hw hR

example (w m : ℕ) (hw : 1 ≤ w) (hm : 32 ≤ m)
    (hR : nearMomentR w (loglogMomentA m) (loglogMomentIndex m)+1 ≤ loglogMomentE m) :
    (1 : ℝ)/(Real.log (Real.log (loglogMomentX w m : ℝ)))^(30*w) <
      (1/2 : ℝ)^(w+1)/((w+1).factorial : ℝ) :=
  loglogMoment_coefficient_gap w m hw hm hR

#print axioms nearMoment_order_le_scale
#print axioms half_factorial_lt_eighth_power
#print axioms coefficient_lt_half_geometric_of_cross
#print axioms log_nearMomentX_lower_power
#print axioms nearMoment_raw_coefficient_gap
#print axioms loglogMoment_coefficient_gap
end Erdos821
