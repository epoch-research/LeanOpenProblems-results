import Submission.StableShiftedPrefixAbsoluteZero
import Submission.LargestPrimeLogAlmostAllEndpoints

/-! Ordinary largest-prime rise proportions are near one half at uniformly
almost all logarithmic endpoints. All windows must have diverging harmonic
mass; this does not settle ordinary natural density. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma shifted_prefix_absolute_perturbation (A M : ℕ) (f g : ℕ → ℝ)
    (he : ∀ n, |f n-g n| ≤ 2) :
    shiftedHarmonicMean A M (fun n => |prefixMean n f|) ≤
      shiftedHarmonicMean A M (fun n => |prefixMean n g|)+
      shiftedHarmonicMean A M (fun n => |f n-g n|)+12/shiftedHarmonicMass A M := by
  have hp (n : ℕ) : |prefixMean n f| ≤ |prefixMean n g|+prefixMean n (fun k => |f k-g k|) := by
    have ht := abs_sub_le (prefixMean n f) (prefixMean n g) 0
    simp only [sub_zero] at ht
    have hb : |prefixMean n f-prefixMean n g| ≤ prefixMean n (fun k => |f k-g k|) := by
      rw [← prefixMean_sub]
      unfold prefixMean
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg n)
    linarith
  have hm := shiftedHarmonicMean_mono A M _ _ hp
  rw [shiftedHarmonicMean_add] at hm
  have hb := shiftedHarmonicMean_prefix_error_bounded (fun n => |f n-g n|) 2 (by norm_num)
    (fun n => by simpa only [abs_abs] using he n) A M
  have hlow := (abs_le.mp hb).1
  norm_num at hlow
  linarith

end Erdos371.FiniteInformation
namespace Erdos371
open Finset Filter FiniteInformation DilationSpectrum
open scoped Topology
set_option autoImplicit false

lemma localFactorSign_shifted_prefix_abs_zero (Q : ℕ) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun N => |prefixMean N (localFactorSign Q)|)) atTop (𝓝 0) :=
  stable_finite_labels_shifted_prefix_abs_zero (localPrimeLabel Q)
    (localPrimeLabel_mean_dilation_defect_zero Q) orderSkew orderSkew_swap orderSkew_abs_le A M hH

/-- The absolute ordinary-prefix bias has mean zero on every moving
harmonic window whose total mass diverges. -/
theorem factorSign_growing_harmonic_prefix_abs_zero (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun N => |prefixMean N factorSign|)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Q,hQ,happrox⟩ := localFactorSign_shifted_harmonic_approximation (ε/4) (by positivity) A M hH
  have hl := localFactorSign_shifted_prefix_abs_zero Q A M hH
  have ht : Tendsto (fun j => (12 : ℝ)/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  filter_upwards [happrox Q le_rfl,hl.eventually_lt_const (by positivity : (0 : ℝ)<ε/4),
    ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/4)] with j ha hl ht
  have hb := shifted_prefix_absolute_perturbation (A j) (M j) factorSign (localFactorSign Q)
    (localFactorSign_error_le_two Q)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (shiftedHarmonicMean_nonneg _ _ _ (fun _ => abs_nonneg _))]
  linarith

/-- Uniformity over all windows, not just one previously chosen sequence.
The required mass bound is not claimed to work for fixed-ratio windows. -/
theorem factorSign_uniform_long_harmonic_prefix_abs (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ A M : ℕ, R ≤ shiftedHarmonicMass A M →
      shiftedHarmonicMean A M (fun N => |prefixMean N factorSign|) < ε := by
  by_contra h
  push_neg at h
  have hn (n : ℕ) : ∃ A M : ℕ, (n+1 : ℝ) ≤ shiftedHarmonicMass A M ∧
      ε ≤ shiftedHarmonicMean A M (fun N => |prefixMean N factorSign|) := h (n+1) (by positivity)
  choose A M hmass hbad using hn
  have hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop :=
    tendsto_atTop_mono hmass (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨j,hj⟩ := ((factorSign_growing_harmonic_prefix_abs_zero A M hH).eventually_lt_const hε).exists
  exact (not_lt_of_ge (hbad j)) hj

lemma shifted_prefix_rise_absolute_identity (A M : ℕ) :
    shiftedHarmonicMean A M (fun N => |prefixMean N factorSign|) =
      2*shiftedHarmonicMean A M (fun N => |(risingCount N : ℝ)/N-1/2|) := by
  rw [← shiftedHarmonicMean_const_mul]
  unfold shiftedHarmonicMean shiftedHarmonicRaw
  congr 1
  apply sum_congr rfl
  intro n _
  dsimp only
  rw [factorSign_prefix_rise_proportion (A+n+1) (by omega),abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ)<2)]

/-- Mean absolute deviation from one half tends to zero under harmonic
sampling of endpoints in any window of diverging harmonic mass. -/
theorem largest_prime_rise_proportions_growing_harmonic_absolute_half (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun N => |(risingCount N : ℝ)/N-1/2|)) atTop (𝓝 0) := by
  have ht := (factorSign_growing_harmonic_prefix_abs_zero A M hH).div_const 2
  simpa only [shifted_prefix_rise_absolute_identity,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    zero_div] using ht

/-- Bad ordinary endpoints have zero density uniformly on long logarithmic
windows. This is not natural density zero of bad endpoints. -/
theorem largest_prime_bad_endpoints_growing_harmonic_zero (ε : ℝ) (hε : 0 < ε) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun N =>
      if ε ≤ |(risingCount N : ℝ)/N-1/2| then (1 : ℝ) else 0)) atTop (𝓝 0) := by
  have ht := (largest_prime_rise_proportions_growing_harmonic_absolute_half A M hH).const_mul ε⁻¹
  simp only [mul_zero] at ht
  apply squeeze_zero (fun j => shiftedHarmonicMean_nonneg _ _ _ (fun N => by split_ifs <;> norm_num)) _ ht
  intro j
  rw [← shiftedHarmonicMean_const_mul]
  apply shiftedHarmonicMean_mono
  intro N
  dsimp only
  rw [inv_mul_eq_div]
  split_ifs with hN
  · exact (one_le_div hε).mpr hN
  · positivity

theorem largest_prime_bad_endpoints_uniform_long_harmonic_zero (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ A M : ℕ, R ≤ shiftedHarmonicMass A M →
      shiftedHarmonicMean A M (fun N =>
        if ε ≤ |(risingCount N : ℝ)/N-1/2| then (1 : ℝ) else 0) < η := by
  by_contra h
  push_neg at h
  have hn (n : ℕ) : ∃ A M : ℕ, (n+1 : ℝ) ≤ shiftedHarmonicMass A M ∧
      η ≤ shiftedHarmonicMean A M (fun N =>
        if ε ≤ |(risingCount N : ℝ)/N-1/2| then (1 : ℝ) else 0) := h (n+1) (by positivity)
  choose A M hmass hbad using hn
  have hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop :=
    tendsto_atTop_mono hmass (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨j,hj⟩ := ((largest_prime_bad_endpoints_growing_harmonic_zero ε hε A M hH).eventually_lt_const hη).exists
  exact (not_lt_of_ge (hbad j)) hj

#print axioms factorSign_growing_harmonic_prefix_abs_zero
#print axioms factorSign_uniform_long_harmonic_prefix_abs
#print axioms largest_prime_rise_proportions_growing_harmonic_absolute_half
#print axioms largest_prime_bad_endpoints_uniform_long_harmonic_zero
end Erdos371
