import Submission.WideReciprocalDensity

/-! Exact-type and permitted-axiom checks for the wide-modulus construction. -/
open Nat Filter
open scoped Classical
namespace Erdos821

#print axioms pairPrimeProducts_mass
#print axioms pair_conductor_majorant_le
#print axioms primitivePoolMean_le_unbalanced
#print axioms pair_composite_error_le
#print axioms wide_primitive_mean_bound
#print axioms wideProductPool_mass_lower
#print axioms wide_composite_error_bound
#print axioms eventually_wide_progression_lower
#print axioms wide_divisor_incidence_le
#print axioms family_progression_weight_le_smooth_count
#print axioms wide_rough_count_le
#print axioms eventually_wide_retained_weight
#print axioms eventually_wide_smooth_prime_count
#print axioms eventually_wide_relative_prime_count
#print axioms wide_prime_reciprocal_divergence

example : ¬Summable (({p : ℕ | p.Prime ∧ ∀ q ∈ (p-1).primeFactors,
    q^40019 ≤ (p-1)^19400} : Set ℕ).indicator (fun p : ℕ => 1/(p : ℝ))) :=
  wide_prime_reciprocal_divergence

example : (19400 : ℚ)/40019 < 1/2 := by norm_num

end Erdos821
