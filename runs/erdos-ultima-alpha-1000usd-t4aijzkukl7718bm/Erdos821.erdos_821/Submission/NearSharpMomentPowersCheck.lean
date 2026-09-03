import Submission.NearSharpMomentPowers

/-! Exact-type and permitted-axiom audit of the subcritical moment powers. -/
open Nat Filter Erdos821 Erdos821.HigherDivisors
open scoped BigOperators

example (K : ℕ) (hK : 2 ≤ K) (α : ℝ) (hα : α < (K : ℝ)-2) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^α ≤
        (∑ p ∈ (X+1).primesBelow, (tau K (p-1) : ℝ)) :=
  frequently_shiftedPrimeMoment_subcritical_power K hK α hα

example (K t : ℕ) (hK : 2 ≤ K) (ht : 2 ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    ∀ B : ℕ, ∃ L : ℕ, B ≤ L ∧
      ((2^(128*t*L) : ℕ) : ℝ)*
        (Real.log ((2^(128*t*L) : ℕ) : ℝ))^((K : ℝ)-2-δ) ≤
          (∑ p ∈ (2^(128*t*L)+1).primesBelow, (tau K (p-1) : ℝ)) :=
  cofinal_shiftedPrimeMoment_subcritical K t hK ht _ (by linarith)

#print axioms harmonic_le_exp_primeTotientMass
#print axioms primeTotientMass_scale_power_lower
#print axioms dyadicReciprocalPrimes_mass_upper
#print axioms primeTotientMass_two_pow_upper
#print axioms primeTotientMass_scale_upper
#print axioms powerPrimePool_mass_lower
#print axioms half_euler_product_card_truncated
#print axioms card_truncated_mass_eq_sum
#print axioms exists_large_primeSubset_mass
#print axioms log_one_add_small_lower
#print axioms powerPrimePool_euler_lower
#print axioms nearMomentPool_bounds
#print axioms nearMomentPool_rough
#print axioms nearMoment_weight_bound
#print axioms nearMoment_combined_error_bound
#print axioms eventually_nearMoment_weighted_error_small
#print axioms eventually_nearMomentR_add_one_le_scale
#print axioms nearMomentP_mass_upper
#print axioms nearMomentR_covers_mean
#print axioms eventually_nearMoment_large_mass
#print axioms eventually_nearMoment_primeLog_lower
#print axioms eventually_log_nearMomentX_le
#print axioms eventually_nearMoment_log_power
#print axioms nearMomentX_tendsto
#print axioms exists_nearMomentExponent_gt
#print axioms frequently_shiftedPrimeMoment_subcritical_power
#print axioms frequently_shiftedPrimeMoment_almost_critical
#print axioms cofinal_nearMoment_dyadic_power
#print axioms cofinal_shiftedPrimeMoment_subcritical
