import Submission.LogLogMomentLower

/-! Exact-type and permitted-axiom checks for the log-log-loss moment bound. -/
open Nat Filter Erdos821 Erdos821.HigherDivisors
open scoped BigOperators

example (K : ℕ) (hK : 2 ≤ K) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^(K-2)/(Real.log (Real.log (X : ℝ)))^(30*(K-1)) ≤
        (∑ p ∈ (X+1).primesBelow, (tau K (p-1) : ℝ)) :=
  frequently_shiftedPrimeMoment_loglog_loss K hK

example (K t : ℕ) (hK : 2 ≤ K) (ht : 2 ≤ t) :
    ∀ B : ℕ, ∃ L : ℕ, B ≤ L ∧
      ((2^(128*t*L) : ℕ) : ℝ)*(Real.log ((2^(128*t*L) : ℕ) : ℝ))^(K-2)/
        (Real.log (Real.log ((2^(128*t*L) : ℕ) : ℝ)))^(30*(K-1)) ≤
          (∑ p ∈ (2^(128*t*L)+1).primesBelow, (tau K (p-1) : ℝ)) :=
  cofinal_shiftedPrimeMoment_loglog_loss K t hK ht

#print axioms nearMoment_weighted_error_of_budget
#print axioms nearMoment_large_mass_of_conditions
#print axioms nearMoment_primeLog_lower_of_conditions
#print axioms log_nearMomentX_le_of_conditions
#print axioms loglogMomentE_eq
#print axioms loglog_nearMomentC_bound
#print axioms loglog_budget_base_bound
#print axioms loglog_budget_degree_bound
#print axioms loglog_budget_exponent_bound
#print axioms loglog_nearMomentBudget_bound
#print axioms loglog_nearMomentR_bound
#print axioms eventually_loglog_finite_conditions
#print axioms nearMoment_lower_conductor_of_R_bound
#print axioms eventually_loglog_primeLog_lower
#print axioms loglogMomentE_square
#print axioms log_loglogMomentE_lower
#print axioms loglogMoment_log_log_lower
#print axioms loglogMomentE_le_log_log_sq
#print axioms loglogMoment_log_log_pos
#print axioms eventually_loglog_log_upper
#print axioms eventually_loglog_shiftedPrimeMoment_lower
#print axioms loglogMomentE_tendsto
#print axioms loglogMomentX_tendsto
#print axioms frequently_shiftedPrimeMoment_loglog_loss
#print axioms cofinal_shiftedPrimeMoment_loglog_loss
