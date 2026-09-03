import Submission.LogTuningExplore

/-! Logarithmic tuning with an odd coordinate thickness. -/
namespace Erdos66OddLogTuning
open Filter Erdos66LogTuning
open scoped Topology
set_option maxHeartbeats 1200000

noncomputable def oddThickness (d : ℝ) (p : ℕ) : ℕ := 2*thickness d p+1

lemma oddThickness_odd (d : ℝ) (p : ℕ) : Odd (oddThickness d p) := ⟨thickness d p,rfl⟩
lemma oddThickness_pos (d : ℝ) (p : ℕ) : 0 < oddThickness d p := by unfold oddThickness; omega

lemma oddThickness_atTop {d : ℝ} (hd : 0 < d) : Tendsto (oddThickness d) atTop atTop := by
  apply tendsto_atTop_mono (fun p ↦ ?_) (thickness_atTop hd)
  unfold oddThickness
  omega

lemma oddThickness_log_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ (oddThickness d p : ℝ)/Real.log p) atTop (𝓝 0) := by
  have hh := ((thickness_log_ratio hd).const_mul 2).add (log_nat_atTop.const_div_atTop 1)
  simp only [mul_zero,add_zero] at hh
  convert hh using 1
  funext p
  simp only [oddThickness,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  ring

lemma log_oddThickness_log_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ Real.log (oddThickness d p)/Real.log p) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (oddThickness_log_ratio hd)
  · filter_upwards [] with p
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · filter_upwards [] with p
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg _)
    have hp : (0 : ℝ) < oddThickness d p := by exact_mod_cast oddThickness_pos d p
    linarith [Real.log_le_sub_one_of_pos hp]

lemma odd_mean_logp {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p ↦ (d/2)*(oddThickness d p : ℝ)^2/Real.log p) atTop (𝓝 2) := by
  have hh := ((tuned_mean_logp hd).add ((thickness_log_ratio hd).const_mul (2*d))).add
    (log_nat_atTop.const_div_atTop (d/2))
  simp only [mul_zero,add_zero] at hh
  convert hh using 1
  funext p
  simp only [oddThickness,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  ring

lemma odd_period_log_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p : ℕ ↦ Real.log ((p*oddThickness d p)^2 : ℕ)/Real.log p) atTop (𝓝 2) := by
  have hh := ((log_oddThickness_log_ratio hd).const_add 1).const_mul 2
  norm_num only [add_zero,mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hK0 : (oddThickness d p : ℝ) ≠ 0 := by exact_mod_cast (oddThickness_pos d p).ne'
  have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  push_cast
  rw [Real.log_pow,Real.log_mul hp0 hK0]
  field_simp
  ring

lemma tuned_odd_mean {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p : ℕ ↦ (d/2)*(oddThickness d p : ℝ)^2/
      Real.log ((p*oddThickness d p)^2 : ℕ)) atTop (𝓝 1) := by
  have hh := (odd_mean_logp hd).div (odd_period_log_ratio hd) (by norm_num : (2 : ℝ) ≠ 0)
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  exact div_div_div_cancel_right₀ hl _ _

lemma odd_period_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p : ℕ ↦ (p*oddThickness d p)^2) atTop atTop := by
  apply tendsto_atTop_mono (fun p ↦ ?_) tendsto_id
  have hp := oddThickness_pos d p
  have hprod : p ≤ p*oddThickness d p := by nlinarith
  exact hprod.trans (Nat.le_pow (by norm_num : 0 < (2 : ℕ)))

end Erdos66OddLogTuning
