import Submission.GrowingSubsetMoments

/-! Exact-type and axiom audit for the growing-subset moment lower bound. -/
open Nat Filter Erdos821 Erdos821.HigherDivisors
open scoped BigOperators

example (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ m : ℕ in atTop,
      ((2^((k*m)*2^(2*m+22)) : ℕ) : ℝ)*
        (Real.log ((2^((k*m)*2^(2*m+22)) : ℕ) : ℝ))^((k : ℝ)/8-1) ≤
          (∑ p ∈ (2^((k*m)*2^(2*m+22))+1).primesBelow,
            (tau (32768*k+1) (p-1) : ℝ)) := by
  simpa only [subsetMomentX_eq_tower,shiftedPrimeMoment] using
    eventually_shiftedPrimeMoment_linear_log_power k hk

example (K : ℕ) (hK : 32769 ≤ K) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^(((K : ℝ)-1)/524288-1) ≤
        (∑ p ∈ (X+1).primesBelow, (tau K (p-1) : ℝ)) :=
  frequently_shiftedPrimeMoment_all_orders_linear K hK

#print axioms reciprocal_totient_multiples_le
#print axioms rough_conductor_majorant_le
#print axioms rough_composite_error_le
#print axioms elementaryMass_succ_identity
#print axioms elementaryMass_factorial_lower
#print axioms primeSubsetModuli_rough
#print axioms primeSubsetModuli_mass
#print axioms primeSubsetModuli_divisor_count
#print axioms binomial_term_le_power
#print axioms primeSubsetModuli_weighted_incidence_le_tau
#print axioms primeSubsetModuli_progression_le_moment
#print axioms small_rough_pool_combined_error
#print axioms subsetMoment_combined_error_bound
#print axioms eventually_subsetMoment_weighted_error_small
#print axioms subsetMoment_mass_factorial_lower
#print axioms subsetMoment_weighted_mass_lower
#print axioms eventually_primeLogDivisorMoment_linear_lower
#print axioms eventually_shiftedPrimeMoment_linear_log_power
#print axioms frequently_shiftedPrimeMoment_linear_log_power
#print axioms tau_order_monotone
#print axioms shiftedPrimeMoment_order_monotone
#print axioms eventually_shiftedPrimeMoment_all_orders_linear
#print axioms frequently_shiftedPrimeMoment_all_orders_linear
#print axioms subsetMomentX_eq_tower
