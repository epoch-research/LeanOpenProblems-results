import Submission.SoftEndpointHazardLimit

/-! Quantitative finite Laplace-to-void errors and an explicit positive
parameter violating the unit-constant endpoint bound. This is only an
auxiliary counterexample, not a disproof of the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real

lemma intervalCount_one_le_of_ne_zero (P : Finset ℕ) (m : ℕ) (r : Phase P)
    (hr : intervalCount P m r ≠ 0) : 1 ≤ intervalCount P m r := by
  have hn : (CoverFibers.phaseSurvivors P m r).card ≠ 0 := by
    intro h
    apply hr
    rw [← CoverFibers.phaseSurvivors_card, h, Nat.cast_zero]
  rw [← CoverFibers.phaseSurvivors_card]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

/-- Integrality, rather than a concentration hypothesis, gives this error. -/
theorem countLaplace_le_void_add_exp (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    countLaplace P t m ≤ coveredFraction P m + exp (-t) := by
  have hh : phaseMean P (fun r => exp (-t*intervalCount P m r)) ≤
      phaseMean P (fun r => (if intervalCount P m r = 0 then 1 else 0)+exp (-t)) := by
    apply phaseMean_mono
    intro r
    by_cases hr : intervalCount P m r = 0
    · simp only [hr, mul_zero, exp_zero, if_true]
      have := (exp_pos (-t)).le
      linarith
    · rw [if_neg hr, zero_add]
      apply exp_le_exp.mpr
      have hs := intervalCount_one_le_of_ne_zero P m r hr
      nlinarith only [mul_nonneg ht (sub_nonneg.mpr hs)]
  rwa [phaseMean_add, phaseMean_const P hP] at hh

/-- The endpoint numerator has the same absolute error budget. -/
theorem endpointLaplace_le_void_add_exp (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    endpointLaplace P t m ≤ coveredEndpointFraction P m + exp (-t) := by
  have hh : phaseMean P (fun r => point P m r*exp (-t*intervalCount P m r)) ≤
      phaseMean P (fun r =>
        point P m r*(if intervalCount P m r = 0 then 1 else 0)+exp (-t)) := by
    apply phaseMean_mono
    intro r
    by_cases hr : intervalCount P m r = 0
    · simp only [hr, mul_zero, exp_zero, if_true, mul_one]
      have := (exp_pos (-t)).le
      linarith
    · rw [if_neg hr, mul_zero, zero_add]
      have he : exp (-t*intervalCount P m r) ≤ exp (-t) := by
        apply exp_le_exp.mpr
        have hs := intervalCount_one_le_of_ne_zero P m r hr
        nlinarith only [mul_nonneg ht (sub_nonneg.mpr hs)]
      rcases point_eq_zero_or_one P m r with hp | hp
      · rw [hp, zero_mul]
        exact (exp_pos _).le
      · simpa only [hp, one_mul] using he
  rwa [phaseMean_add, phaseMean_const P hP] at hh

namespace HazardExample

/-- An explicit parameter, with all rational arithmetic checked by Lean. -/
theorem explicit_unit_endpoint_failure :
    ¬SoftEndpointBound 1 (log 10000000000) := by
  intro h
  have ht : 0 < log (10000000000 : ℝ) := log_pos (by norm_num)
  have hu := endpointLaplace_le_void_add_exp primes primes_prime 9
    (log 10000000000) ht.le
  rw [actual_endpoint_void_fraction, exp_neg, exp_log (by norm_num)] at hu
  have hl := coveredFraction_le_countLaplace primes (log 10000000000) 9
  rw [actual_void_fraction] at hl
  have hh := h primes primes_prime 9
  simp only [one_mul] at hh
  have hc : (24 : ℝ)/257130951+(10000000000 : ℝ)⁻¹ <
      density primes*((48 : ℝ)/257130951) := by
    norm_num [density, primes]
  have hm := mul_le_mul_of_nonneg_left hl (density_pos primes primes_prime).le
  exact (hu.trans_lt hc).not_ge (hm.trans hh)

#print axioms explicit_unit_endpoint_failure
end HazardExample
#print axioms countLaplace_le_void_add_exp
#print axioms endpointLaplace_le_void_add_exp
end Erdos970.GapAverages
