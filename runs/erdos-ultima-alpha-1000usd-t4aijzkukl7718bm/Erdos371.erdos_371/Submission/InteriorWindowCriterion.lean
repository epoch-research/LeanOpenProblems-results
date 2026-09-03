import Submission.HarmonicWindowConverse
import Submission.DyadicTwoSidedBoundary

/-! An exact criterion for the original density statement using two fixed
harmonic windows of the surviving signed interior. Neither interior window
limit is asserted here. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma dyadicInteriorSign_abs_le (n : ℕ) : |dyadicInteriorSign n|≤1 := by
  unfold dyadicInteriorSign
  split_ifs
  · norm_num
  · simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))

lemma density_iff_interior_prefixMean_zero :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N => prefixMean N dyadicInteriorSign) atTop (𝓝 0) := by
  have he : Tendsto (fun N => prefixMean N factorSign-prefixMean N dyadicInteriorSign)
      atTop (𝓝 0) := by
    simpa only [prefixMean_sub] using dyadic_boundary_natural_mean_zero
  have hd : {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N => prefixMean N factorSign) atTop (𝓝 0) := by
    simpa only [prefixMean,factorSign_sum_eq_count_difference] using density_iff_signed_count
  rw [hd]
  constructor
  · intro h
    simpa only [sub_sub_cancel,sub_self] using h.sub he
  · intro h
    simpa only [add_sub_cancel,add_zero] using h.add he

/-- The conjecture is equivalent to these TWO unnormalized signed interior
window limits. The previously controlled moving boundaries disappear from
both windows; the interior cancellation is still a substantive hypothesis. -/
theorem density_iff_two_interior_harmonic_windows :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N => rawHarmonicSum dyadicInteriorSign (2*N)-rawHarmonicSum dyadicInteriorSign N)
        atTop (𝓝 0) ∧
      Tendsto (fun N => rawHarmonicSum dyadicInteriorSign (3*N)-rawHarmonicSum dyadicInteriorSign N)
        atTop (𝓝 0) := by
  rw [density_iff_interior_prefixMean_zero]
  exact prefixMean_zero_iff_two_harmonic_windows dyadicInteriorSign dyadicInteriorSign_abs_le

/-- The full and interior window sums differ by a quantity tending to zero
at every fixed positive integer ratio, not just at ratios two and three. -/
theorem dyadic_boundary_harmonic_window_zero (a : ℕ) (ha : 0<a) :
    Tendsto (fun N =>
      (rawHarmonicSum factorSign (a*N)-rawHarmonicSum factorSign N)-
      (rawHarmonicSum dyadicInteriorSign (a*N)-rawHarmonicSum dyadicInteriorSign N))
      atTop (𝓝 0) := by
  obtain ⟨L,hL⟩ := dyadic_boundary_rawHarmonic_converges
  have ht : Tendsto (fun N : ℕ => a*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by
      simpa only [id_eq,one_mul] using Nat.mul_le_mul_right N (show 1≤a from ha)) tendsto_id
  have h := (hL.comp ht).sub hL
  simp only [sub_self] at h
  apply h.congr
  intro N
  simp only [Function.comp_apply,rawHarmonicSum,sub_div,sum_sub_distrib]
  ring

#print axioms density_iff_two_interior_harmonic_windows
#print axioms dyadic_boundary_harmonic_window_zero
end Erdos371
