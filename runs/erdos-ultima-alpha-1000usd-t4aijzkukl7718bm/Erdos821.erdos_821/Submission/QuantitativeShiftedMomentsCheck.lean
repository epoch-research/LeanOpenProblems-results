import Submission.QuantitativeShiftedMoments

/-! Exact-type and axiom checks for quantitative shifted-prime divisor moments. -/
open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open HigherDivisors

#print axioms widePrimePool_separated
#print axioms prime_pool_composite_error_le
#print axioms logMomentModuli_mass_lower
#print axioms logMoment_block_primitive_bound
#print axioms logMoment_primitive_bound
#print axioms family_progression_le_prime_factor_mean
#print axioms logMoment_combined_error_bound
#print axioms eventually_logMoment_combined_error_small
#print axioms eventually_shiftedPrimeFactorMangoldt_lower
#print axioms pow_primeFactors_card_le_tau
#print axioms primeLogDivisorMoment_tangent
#print axioms eventually_primeLogDivisorMoment_lower
#print axioms eventually_shiftedPrimeMoment_log_power_lower
#print axioms logMomentX_eq_tower
#print axioms eventually_shiftedPrimeMoment_two_log_power_lower

example : ∀ᶠ m : ℕ in atTop, ∀ k : ℕ, 2 ≤ k →
    ((2^(2^(2*m+16)) : ℕ) : ℝ)*
      (Real.log ((2^(2^(2*m+16)) : ℕ) : ℝ))^(Real.log (k : ℝ)/131072-1) ≤
        ∑ p ∈ (2^(2^(2*m+16))+1).primesBelow, (tau k (p-1) : ℝ) := by
  simpa only [logMomentX_eq_tower,shiftedPrimeMoment] using
    eventually_shiftedPrimeMoment_log_power_lower

end Erdos821
