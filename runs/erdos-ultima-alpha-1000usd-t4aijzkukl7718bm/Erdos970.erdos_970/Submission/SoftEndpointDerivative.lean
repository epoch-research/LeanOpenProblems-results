import Submission.WeakSoftEndpointReduction
import Submission.GapVarianceSubadditive

/-! The exact initial slope of the tilted endpoint probability. The result
is uniform in interval length but is only a derivative at parameter zero;
it supplies no common positive parameter in an endpoint criterion. -/
namespace Erdos970.GapAverages
open Finset Real

noncomputable def endpointSlope (P : Finset ℕ) (m : ℕ) : ℝ :=
  (m : ℝ)*density P^2 -
    phaseMean P (fun r => intervalCount P m r * point P m r)

lemma endpointSlope_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    0 ≤ endpointSlope P m :=
  sub_nonneg.mpr (phaseMean_count_point_le P hP m)

/-- The initial covariance defect is an exact sum of nonnegative fractional
remainders, with coefficient mass equal to the sieve density. -/
lemma endpointSlope_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    endpointSlope P m = ∑ Q ∈ P.powerset, pairWeight P Q *
      ((m : ℝ)/(∏ p ∈ Q, (p : ℝ)) - (m/(∏ p ∈ Q, p) : ℕ)) := by
  rw [endpointSlope, phaseMean_count_point_exact P hP, sum_pairKernel_exact P hP,
    ← pairWeight_mass P hP, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro Q hQ
  ring

/-- Unlike a bound proportional to m, this estimate is uniform in the
interval length. It does not bound higher tilted derivatives. -/
theorem endpointSlope_le_density (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) : endpointSlope P m ≤ density P := by
  rw [endpointSlope_expansion P hP, ← sum_pairWeight P hP]
  apply sum_le_sum
  intro Q hQ
  have hQP := mem_powerset.mp hQ
  have hD : 0 < ∏ p ∈ Q, p := prod_pos (fun p hp => (hP p (hQP hp)).pos)
  have hDR : (0 : ℝ) < ∏ p ∈ Q, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hD
  have hl : (m : ℝ) < (∏ p ∈ Q, (p : ℝ)) * ((m/(∏ p ∈ Q, p) : ℕ)+1) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.lt_mul_div_succ m hD
  have hf : (m : ℝ)/(∏ p ∈ Q, (p : ℝ)) - (m/(∏ p ∈ Q, p) : ℕ) ≤ 1 := by
    have hh : (m : ℝ)/(∏ p ∈ Q, (p : ℝ)) <
        (m/(∏ p ∈ Q, p) : ℕ)+1 := (div_lt_iff₀ hDR).mpr (by nlinarith [hl])
    linarith
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hf (pairWeight_nonneg P Q hP)

lemma countLaplace_parameter_zero (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) : countLaplace P 0 m = 1 := by
  unfold countLaplace
  simp only [neg_zero, zero_mul, exp_zero]
  exact phaseMean_const P hP 1

lemma endpointLaplace_parameter_zero (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) : endpointLaplace P 0 m = density P := by
  unfold endpointLaplace
  simp only [neg_zero, zero_mul, exp_zero, mul_one]
  exact phaseMean_point P hP m

lemma hasDerivAt_countLaplace_zero (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    HasDerivAt (fun t => countLaplace P t m) (-((m : ℝ)*density P)) 0 := by
  have h (r : Phase P) : HasDerivAt
      (fun t : ℝ => exp (-t*intervalCount P m r)) (-intervalCount P m r) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).neg.mul_const (intervalCount P m r)).exp
  have hs := (HasDerivAt.fun_sum (u := (univ : Finset (Phase P)))
    (fun r _ => h r)).div_const (∏ p : P, (p.val : ℝ))
  have he : (∑ r : Phase P, -intervalCount P m r)/(∏ p : P, (p.val : ℝ)) =
      -((m : ℝ)*density P) := by
    rw [sum_neg_distrib, neg_div]
    exact congrArg Neg.neg (phaseMean_count P hP m)
  simpa only [he, countLaplace, phaseMean] using hs

lemma hasDerivAt_endpointLaplace_zero (P : Finset ℕ) (m : ℕ) :
    HasDerivAt (fun t => endpointLaplace P t m)
      (-phaseMean P (fun r => intervalCount P m r * point P m r)) 0 := by
  have h (r : Phase P) : HasDerivAt
      (fun t : ℝ => point P m r * exp (-t*intervalCount P m r))
      (-(intervalCount P m r * point P m r)) 0 := by
    have hh : HasDerivAt (fun t : ℝ => exp (-t*intervalCount P m r))
        (-intervalCount P m r) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).neg.mul_const (intervalCount P m r)).exp
    simpa only [mul_neg, neg_mul, mul_comm] using hh.const_mul (point P m r)
  have hs := (HasDerivAt.fun_sum (u := (univ : Finset (Phase P)))
    (fun r _ => h r)).div_const (∏ p : P, (p.val : ℝ))
  simpa only [endpointLaplace, phaseMean, sum_neg_distrib, neg_div] using hs

/-- The quotient is the endpoint probability under the actual finite Gibbs
weight exp(-t*S_m), not an independent-row approximation. -/
noncomputable def tiltedEndpoint (P : Finset ℕ) (m : ℕ) (t : ℝ) : ℝ :=
  endpointLaplace P t m / countLaplace P t m

lemma tiltedEndpoint_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    tiltedEndpoint P m 0 = density P := by
  simp [tiltedEndpoint, countLaplace_parameter_zero P hP,
    endpointLaplace_parameter_zero P hP]

/-- Exact derivative, with both the numerator and normalizer differentiated. -/
theorem hasDerivAt_tiltedEndpoint_zero (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    HasDerivAt (tiltedEndpoint P m) (endpointSlope P m) 0 := by
  have hh := (hasDerivAt_endpointLaplace_zero P m).div
    (hasDerivAt_countLaplace_zero P hP m)
    (by rw [countLaplace_parameter_zero P hP]; norm_num)
  rw [countLaplace_parameter_zero P hP, endpointLaplace_parameter_zero P hP] at hh
  convert hh using 1
  unfold endpointSlope
  ring

/-- Initial normalized slope lies in [0,1]. No uniform positive neighborhood
or positive-parameter lower bound follows merely from this derivative. -/
theorem tiltedEndpoint_initial_derivative_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    0 ≤ deriv (tiltedEndpoint P m) 0 ∧ deriv (tiltedEndpoint P m) 0 ≤ density P := by
  rw [(hasDerivAt_tiltedEndpoint_zero P hP m).deriv]
  exact ⟨endpointSlope_nonneg P hP m, endpointSlope_le_density P hP m⟩

#print axioms endpointSlope_le_density
#print axioms hasDerivAt_tiltedEndpoint_zero
#print axioms tiltedEndpoint_initial_derivative_bounds
end Erdos970.GapAverages
