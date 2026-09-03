import Submission.AutocorrelationAbelExplore

/-! An unrestricted mean-square autocorrelation necessary condition for a
hypothetical logarithmic representation witness. It is not a disproof. -/
namespace Erdos66WitnessAutocorrelation
open Erdos66NaturalAutocorrelation Erdos66AutocorrelationAbel
  Erdos66Generating Erdos66Fractional Erdos66FractionalFourthPower
  Erdos66SquareRootFluctuation Erdos66AbelErrorEnergy
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 1800000

noncomputable def squareKernel (r : ℝ) : ℝ := (1-r)/(-Real.log (1-r))^2

lemma squareKernel_nonneg {r : ℝ} (hr : r<1) : 0 ≤ squareKernel r :=
  div_nonneg (sub_nonneg.mpr hr.le) (sq_nonneg _)

lemma harmonicSqSeries_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r<1) : 0<harmonicSqSeries r := by
  have hh := (summable_harmonic_sq hr0 hr1).sum_le_tsum (s := {0})
    (fun n _ ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr0 n))
  have h1 : (1:ℝ) ≤ harmonicSqSeries r := by
    simpa only [Finset.sum_singleton,harmonic,Finset.sum_range_one,Nat.cast_zero,
      zero_add,Nat.cast_one,inv_one,Rat.cast_one,one_pow,pow_zero,mul_one] using hh
  exact zero_lt_one.trans_le h1

lemma harmonicSqSeries_normalized_bound {r : ℝ} (hr0 : 0<r) (hr1 : r<1)
    (hL : 1 ≤ -Real.log (1-r)) : harmonicSqSeries r*squareKernel r ≤ 6 := by
  have ht := sub_pos.mpr hr1
  have hln : -Real.log (1-r)≠0 := by linarith
  have hh := mul_le_mul_of_nonneg_right (harmonic_sq_series_bound hr0 hr1 hL)
    (squareKernel_nonneg hr1)
  have he : (6*(-Real.log (1-r))^2/(1-r))*squareKernel r=6 := by
    dsimp [squareKernel]
    have hlog : Real.log (1-r)≠0 := neg_ne_zero.mp hln
    field_simp [hlog,ht.ne']
  exact hh.trans_eq he

/-- The representation error has the expected little-o bound for its
logarithmic-square Abel normalization. -/
theorem witness_normalized_error_energy_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ series (errorSq A c) r*squareKernel r) (𝓝[<] 1) (𝓝 0) := by
  have hu := (witness_error_ratio_zero h).mul_const 6
  simp only [zero_mul] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_nonneg (tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr.1.le n)))
      (squareKernel_nonneg hr.2)
  · filter_upwards [unit_interval_eventually,
      negative_log_one_sub.eventually_ge_atTop 1] with r hr hL
    have hH := harmonicSqSeries_pos hr.1.le hr.2
    have hE : 0 ≤ series (errorSq A c) r :=
      tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr.1.le n))
    calc
      _ = (series (errorSq A c) r/harmonicSqSeries r)*(harmonicSqSeries r*squareKernel r) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonicSqSeries_normalized_bound hr.1 hr.2 hL)
        (div_nonneg hE hH.le)

lemma weightedCorr_sqrt_scale {c : ℝ} (hc : 0 ≤ c) (f : ℕ → ℝ) (r : ℝ) (h : ℕ) :
    weightedCorr (fun n ↦ Real.sqrt c*f n) r h=c*weightedCorr f r h := by
  unfold weightedCorr
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  calc
    _ = (Real.sqrt c)^2*(f n*f (n+h)*r^(2*n+h)) := by ring
    _ = _ := by rw [Real.sq_sqrt hc]

noncomputable def corrErrorEnergy (A : Set ℕ) (c r : ℝ) : ℝ :=
  ∑' h, (weightedCorr (indicator A) r h-c*weightedCorr profile r h)^2

/-- This quantitative bound holds for every natural set A and every c>=0,
not only for hypothetical witnesses. All shifts here are natural, not cyclic. -/
theorem natural_corr_error_bound (A : Set ℕ) {c r : ℝ}
    (hc : 0 ≤ c) (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun h ↦ (weightedCorr (indicator A) r h-c*weightedCorr profile r h)^2) ∧
      corrErrorEnergy A c r ≤ series (errorSq A c) r := by
  have hf := summable_indicator A (r := r) (by simpa only [abs_of_pos hr0] using hr1)
  have hg : Summable (fun n ↦ (Real.sqrt c*profile n)*r^n) := by
    simpa only [pow_one,mul_assoc] using
      (summable_profile_power_weighted hr0.le hr1 1).mul_left (Real.sqrt c)
  have hcA (n : ℕ) : sumConv (indicator A) (indicator A) n=(sumRep A n : ℝ) :=
    sum_indicator_antidiagonal A n
  have hE : Summable (fun n ↦ (sumConv (indicator A) (indicator A) n-
      sumConv (fun n ↦ Real.sqrt c*profile n) (fun n ↦ Real.sqrt c*profile n) n)^2*r^n) := by
    simpa only [hcA,scaled_profile_convolution hc,errorSq] using summable_errorSq A c hr0.le hr1
  have hh := weighted_corr_error hr0.le hr1 hf hg hE
  simp_rw [← weightedCorr_eq,weightedCorr_sqrt_scale hc] at hh
  simpa only [corrErrorEnergy,series,errorSq,hcA,scaled_profile_convolution hc] using hh

/-- A witness must approximate the fractional profile in the squared norm
of its full weighted autocorrelation sequence, at scale log²/(1-r). -/
theorem witness_normalized_corr_error_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ corrErrorEnergy A c r*squareKernel r) (𝓝[<] 1) (𝓝 0) := by
  have hc := Erdos66Explore.limit_nonneg h
  apply squeeze_zero' _ _ (witness_normalized_error_energy_zero h)
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_nonneg (tsum_nonneg (fun _ ↦ sq_nonneg _)) (squareKernel_nonneg hr.2)
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_le_mul_of_nonneg_right (natural_corr_error_bound A hc hr.1 hr.2).2
      (squareKernel_nonneg hr.2)

end Erdos66WitnessAutocorrelation
