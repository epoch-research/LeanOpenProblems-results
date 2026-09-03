import FormalConjecturesUtil
import Submission.PrimePowerRectangles

/-! A positive linear lower bound for the UNSIGNED logarithmically weighted
restriction correction, along twentieth-power cutoffs. Thus this error cannot
be discarded by a mean-absolute bound. No assertion about its signed mean is
made, and this is not a disproof of Erdős 371. -/

namespace Erdos371UnsignedCorrectionLowerBound

open Finset Filter Erdos371PrimeLogMass Erdos371PrimePowerRectangles
open Erdos371UnsignedRestrictionMass
open scoped Topology

lemma power_tendsto {k : ℕ} (hk : 0<k) : Tendsto (fun X : ℕ => X^k) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (max B 1)] with X hX
  have hx : 0<X := by omega
  have hp : X ≤ X^k := by simpa only [pow_one] using
    (Nat.pow_le_pow_right hx (show 1 ≤ k by omega))
  omega

noncomputable def scaledMass (X k : ℕ) : ℝ := mass (X^k)/Real.log (X : ℝ)

lemma scaledMass_tendsto {k : ℕ} (hk : 0<k) :
    Tendsto (fun X : ℕ => scaledMass X k) atTop (𝓝 (k : ℝ)) := by
  have hh := (mass_log_ratio_tendsto_one.comp (power_tendsto hk)).mul_const (k : ℝ)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 1] with X hX
  have hl : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp only [Function.comp_apply,Nat.cast_pow,Real.log_pow,scaledMass]
  field_simp

lemma piece_eq_scaled {X : ℕ} (hX : 1<X) (k : ℕ) :
    piece X k = (scaledMass X (j k)/20) *
      ((scaledMass X (k+1)-scaledMass X k)/(k+1 : ℕ)) := by
  have hl : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  have hk0 : ((k+1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold piece scaledMass
  simp only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat]
  field_simp

lemma piece_tendsto {k : ℕ} (hk : k ∈ Icc 1 18) :
    Tendsto (fun X : ℕ => piece X k) atTop
      (𝓝 ((j k : ℝ)/20 * (1/(k+1 : ℕ)))) := by
  have hk' := mem_Icc.mp hk
  have hj : 0<j k := by unfold j; omega
  have hh := ((scaledMass_tendsto hj).div_const 20).mul
    (((scaledMass_tendsto (show 0<k+1 by omega)).sub
      (scaledMass_tendsto (show 0<k by omega))).div_const ((k+1 : ℕ) : ℝ))
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left] at hh
  simp only [Nat.cast_add,Nat.cast_one]
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 1] with X hX
  simpa only [Nat.cast_add,Nat.cast_one] using (piece_eq_scaled hX k).symm

lemma lower_tendsto : Tendsto lower atTop
    (𝓝 (∑ k ∈ Icc 1 18, (j k : ℝ)/20 * (1/(k+1 : ℕ)))) :=
  tendsto_finset_sum _ (fun _ hk => piece_tendsto hk)

lemma coefficient_bound :
    (51/50 : ℝ) < 2*(∑ k ∈ Icc 1 18, (j k : ℝ)/20 * (1/(k+1 : ℕ))) := by
  norm_num [j,Finset.sum_Icc_succ_top]

/-- The unsigned error is at least `N/50` on all sufficiently large cutoffs
of the form `N=X^20`. The coefficient is deliberately below the computed
rectangle lower bound. -/
theorem eventually_positive_unsigned_mass : ∀ᶠ X : ℕ in atTop,
    (1/50 : ℝ) ≤ exceptionMass (X^20)/(X^20 : ℕ) := by
  have hp : Tendsto (fun X : ℕ => X^20) atTop atTop := power_tendsto (by norm_num)
  have hs := Erdos371ReflectionRange.semiCount_ratio_zero.comp hp
  have hh := ((lower_tendsto.const_mul 2).sub (tendsto_const_nhds (x := (1 : ℝ)))).sub
    (hs.const_mul 2)
  simp only [mul_zero,sub_zero] at hh
  have hc : (1/50 : ℝ) <
      2*(∑ k ∈ Icc 1 18, (j k : ℝ)/20 * (1/(k+1 : ℕ)))-1 := by
    linarith [coefficient_bound]
  have he := hh.eventually (lt_mem_nhds hc)
  filter_upwards [he,eventually_gt_atTop 1] with X hgood hX
  have hN : 1<X^20 := power_gt_one hX (by norm_num)
  have hmain := lower_le_mainMass hX
  have herr := exception_main_lower hN
  dsimp only [Function.comp_apply] at hgood
  change (1/50 : ℝ) < 2*lower X-1-2*((Erdos371ReflectionRange.semiCount (X^20) : ℝ)/(X^20 : ℕ)) at hgood
  rw [mul_div_assoc] at herr
  linarith

/-- In particular, the unsigned correction is not `o(N)`. This leaves open
whether the signed difference of the two correction counts cancels. -/
theorem unsigned_mass_not_mean_zero :
    ¬ Tendsto (fun N : ℕ => exceptionMass N/N) atTop (𝓝 0) := by
  intro h
  have hh := h.comp (power_tendsto (k := 20) (by norm_num))
  have he := hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/50))
  obtain ⟨X,hX,hX'⟩ := (eventually_positive_unsigned_mass.and he).exists
  exact (not_lt_of_ge hX) hX'

end Erdos371UnsignedCorrectionLowerBound

#print axioms Erdos371UnsignedCorrectionLowerBound.eventually_positive_unsigned_mass
#print axioms Erdos371UnsignedCorrectionLowerBound.unsigned_mass_not_mean_zero
