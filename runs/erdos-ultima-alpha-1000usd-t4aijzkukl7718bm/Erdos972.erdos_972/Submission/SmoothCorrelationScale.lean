import Submission.SmoothCorrelationApprox

/-! A concrete vanishing smoothing parameter gives an o(N) comparison with
the Mangoldt correlation. At this same parameter, exponential damping at
any polynomial divisor cutoff tends to one, not zero. No smoothed
correlation lower bound is supplied here. -/
namespace Erdos972SmoothCorrelationScale

open Filter
open scoped Topology
open Erdos972PrimePowerError Erdos972SmoothCorrelationApprox

noncomputable def smoothingParameter (α : ℝ) (N : ℕ) : ℝ :=
  1 / (1+Real.log (floorMul α N))^5

lemma smoothingParameter_pos (α : ℝ) (N : ℕ) : 0 < smoothingParameter α N := by
  unfold smoothingParameter
  positivity [Real.log_natCast_nonneg (floorMul α N)]

lemma smoothingParameter_small (α : ℝ) (N : ℕ) :
    smoothingParameter α N * Real.log (floorMul α N) ≤ 1 := by
  let L := Real.log (floorMul α N)
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have hbase : 1 ≤ 1+L := by linarith
  have hpow : 1+L ≤ (1+L)^5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 5)
  change (1 / (1+L)^5) * L ≤ 1
  rw [one_div_mul_eq_div]
  exact (div_le_one (by positivity)).mpr (by linarith)

lemma normalized_error_bound {α : ℝ} (hα : 1 ≤ α) {N : ℕ} (hN : 1 ≤ N) :
    |smoothCorrelation (smoothingParameter α N) α N - mangoldtCorrelation α N| / N ≤
      (1+α)/(1+Real.log N) := by
  let M := floorMul α N
  have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hMpos : 0 < M := floorMul_pos hα hN
  have hNM : Real.log N ≤ Real.log M := Real.log_le_log hNpos
    (Nat.cast_le.mpr (self_le_floorMul hα N))
  have hbaseM : 0 < 1+Real.log M := by positivity [Real.log_natCast_nonneg M]
  have hbaseN : 0 < 1+Real.log N := by positivity [Real.log_natCast_nonneg N]
  have hMbound : (M:ℝ) ≤ α*N := floorMul_le_real hα le_rfl
  have hE := smoothCorrelation_error_bound hα (smoothingParameter_pos α N) N
    (smoothingParameter_small α N)
  have hE' : |smoothCorrelation (smoothingParameter α N) α N - mangoldtCorrelation α N| ≤
      ((N:ℝ)+M)/(1+Real.log M) := by
    apply hE.trans_eq
    change (1/(1+Real.log M)^5) * ((N:ℝ)+M) * (1+Real.log M)^4 = _
    field_simp
  calc
    _ ≤ (((N:ℝ)+M)/(1+Real.log M))/N := div_le_div_of_nonneg_right hE' hNpos.le
    _ = (((N:ℝ)+M)/N)/(1+Real.log M) := by ring
    _ ≤ (1+α)/(1+Real.log M) := by
      apply div_le_div_of_nonneg_right _ hbaseM.le
      apply (div_le_iff₀ hNpos).mpr
      nlinarith only [hMbound]
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) hbaseN (by linarith)

/-- Uniformly in the natural cutoff, with t_N approximately (log N)^(-5),
the smoothed and genuine Mangoldt correlations differ by o(N). -/
theorem variable_smoothing_error_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ =>
      (smoothCorrelation (smoothingParameter α N) α N - mangoldtCorrelation α N)/N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => 1+Real.log N) atTop atTop := by
    apply tendsto_atTop_mono (fun N : ℕ => show Real.log N ≤ 1+Real.log N by linarith)
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (1+α)/(1+Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  exact normalized_error_bound hα hN

lemma parameter_mul_log_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ => smoothingParameter α N * Real.log N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => 1+Real.log N) atTop atTop := by
    apply tendsto_atTop_mono (fun N : ℕ => show Real.log N ≤ 1+Real.log N by linarith)
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (1:ℝ)/(1+Real.log N)^4) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : (4:ℕ) ≠ 0)).comp hlog)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [] with N
    exact mul_nonneg (smoothingParameter_pos α N).le (Real.log_natCast_nonneg N)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hlogN := Real.log_natCast_nonneg N
    have hNM : Real.log N ≤ Real.log (floorMul α N) :=
      Real.log_le_log (Nat.cast_pos.mpr hN) (Nat.cast_le.mpr (self_le_floorMul hα N))
    have hbase : 0 < 1+Real.log N := by positivity
    have hparam : smoothingParameter α N ≤ 1/(1+Real.log N)^5 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ hbase.le (by linarith) 5
    calc
      _ ≤ (1/(1+Real.log N)^5)*(Real.log N) := mul_le_mul_of_nonneg_right hparam hlogN
      _ ≤ (1/(1+Real.log N)^5)*(1+Real.log N) := by gcongr; linarith
      _ = 1/(1+Real.log N)^4 := by field_simp

/-- For a divisor cutoff D=N^delta, its exponential damping D^(-t_N)
approaches one. Thus a bound requiring this factor to vanish cannot simply
be applied at the parameter in the preceding comparison theorem. -/
theorem polynomial_cutoff_damping_tendsto_one {α : ℝ} (hα : 1 ≤ α) (δ : ℝ) :
    Tendsto (fun N : ℕ => Real.exp (-δ * smoothingParameter α N * Real.log N))
      atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => -δ * (smoothingParameter α N * Real.log N))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (parameter_mul_log_tendsto hα).const_mul (-δ)
  have hh := (Real.continuous_exp.tendsto (0:ℝ)).comp hz
  simpa only [Real.exp_zero, mul_assoc] using hh

#print axioms variable_smoothing_error_tendsto
#print axioms polynomial_cutoff_damping_tendsto_one

end Erdos972SmoothCorrelationScale
