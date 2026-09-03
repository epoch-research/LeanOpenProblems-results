import Submission.OrdinaryDivisorMean

/-! Full damped correlation means for every irrational slope, along all
natural input cutoffs. Damping is fixed before the cutoff tends to infinity.
No simultaneous prime-pair lower bound or uniformity at zero damping is
claimed. -/
namespace Erdos972OrdinaryDampedCorrelation

open Finset Filter
open scoped Topology
open Erdos972OrdinaryDivisorMean Erdos972FixedDampedCorrelation
open Erdos972SmoothDivisorTail Erdos972SmoothCorrelationApprox
open Erdos972DampedMeanZeta Erdos972DivisorCovariance

/-- The selected-scale restriction can be removed for fixed positive damping. -/
theorem full_damped_mean {α t : ℝ} (hα : 1 ≤ α) (hI : Irrational α) (ht : 0 < t) :
    Tendsto (fun N : ℕ => fullExpCorrelation t α N/(N : ℝ)) atTop (𝓝 ((dampedMean t)^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε/3 := by positivity
  have hm := ((divisorMean_tendsto ht).pow 2).sub_const ((dampedMean t)^2)
  have hma := hm.abs
  simp only [sub_self, abs_zero] at hma
  obtain ⟨D, hD, hmean⟩ := ((eventually_uniform_correlation_cutoff hα ht hthird).and
    ((tendsto_order.mp hma).2 (ε/3) hthird)).exists
  have htr := (Metric.tendsto_nhds.mp (truncated_correlation_mean hα hI t D)) (ε/3) hthird
  filter_upwards [htr, eventually_ge_atTop (1 : ℕ)] with N htr hN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have htail : |fullExpCorrelation t α N/(N : ℝ)-truncatedExpCorrelation t α D N/(N : ℝ)| ≤ ε/3 := by
    rw [← sub_div, abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).mpr (hD N)
  rw [Real.dist_eq] at htr ⊢
  have hh := (abs_sub_le (fullExpCorrelation t α N/(N : ℝ))
    (truncatedExpCorrelation t α D N/(N : ℝ)) ((dampedMean t)^2)).trans
    (add_le_add htail (abs_sub_le _ ((divisorMean D (dampedCoefficient t))^2) _))
  linarith only [hh, htr, hmean]

/-- The corresponding corrected smoothed Mangoldt mean. This is still
only a fixed-positive-parameter theorem. -/
theorem full_smooth_mean {α t : ℝ} (hα : 1 ≤ α) (hI : Irrational α) (ht : 0 < t) :
    Tendsto (fun N : ℕ => smoothCorrelation t α N/(N : ℝ)) atTop (𝓝 ((dampedMean t/t)^2)) := by
  have he : Tendsto (fun N : ℕ =>
      (fullExpCorrelation t α N-t^2*smoothCorrelation t α N)/(N : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    filter_upwards with N
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (full_minus_scaled_smooth hα ht N) (Nat.cast_nonneg N)
  have hh := ((full_damped_mean hα hI ht).sub he).div_const (t^2)
  simp only [sub_zero] at hh
  convert hh using 1
  · funext N
    field_simp
    ring
  · rw [div_pow]

/-- This is the outer scalar limit in the iterated limit. It does not
interchange the damping and input-cutoff limits. -/
theorem iterated_smooth_mean_tendsto_one :
    Tendsto (fun t : ℝ => (dampedMean t/t)^2) (𝓝[>] 0) (𝓝 1) := by
  simpa only [one_pow] using dampedMean_div_tendsto_one.pow 2

#print axioms full_damped_mean
#print axioms full_smooth_mean
#print axioms iterated_smooth_mean_tendsto_one

end Erdos972OrdinaryDampedCorrelation
