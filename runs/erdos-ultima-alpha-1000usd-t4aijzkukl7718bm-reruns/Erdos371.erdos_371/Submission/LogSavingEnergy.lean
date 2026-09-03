import FormalConjecturesUtil
import Submission.RankinSmoothCount
import Submission.ElementaryEnergy

/-! Unconditional logarithmic savings over the quadratic winning-prime energy
bound. These do NOT reach the near-linear energy needed for the conjecture. -/

namespace Erdos371LogSavingEnergy

open Filter Erdos371PrimeDiscrepancy Erdos371PrimeEnergy
open Erdos371ElementaryEnergy Erdos371RankinSmoothCount
open scoped Topology

noncomputable def cutoff (m N : ℕ) : ℕ := ⌈Real.log (N:ℝ)^m⌉₊
noncomputable def delta (m : ℕ) : ℝ := 1/(2*(m:ℝ))

lemma delta_bounds {m : ℕ} (hm : 0 < m) : 0 < delta m ∧ delta m ≤ 1/2 := by
  have hh : (1:ℝ) ≤ m := by exact_mod_cast hm
  unfold delta
  constructor
  · positivity
  · apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*(m:ℝ)) (by norm_num : (0:ℝ)<2)).mpr
    linarith

lemma cutoff_pos {m N : ℕ} (hN : 1 < N) : 0 < cutoff m N := by
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hh := Nat.le_ceil (Real.log (N:ℝ)^m)
  have hp : 0 < Real.log (N:ℝ)^m := pow_pos hlog m
  have : (0:ℝ) < cutoff m N := hp.trans_le hh
  exact Nat.cast_pos.mp this

lemma cutoff_power_bound {m N : ℕ} (hm : 0 < m) (hN : 1 ≤ Real.log (N:ℝ)) :
    (cutoff m N:ℝ)^(delta m) ≤ 2*Real.sqrt (Real.log (N:ℝ)) := by
  obtain ⟨hd0,hd1⟩ := delta_bounds hm
  have hl : 0 < Real.log (N:ℝ) := lt_of_lt_of_le zero_lt_one hN
  have hh : (cutoff m N:ℝ) ≤ 2*Real.log (N:ℝ)^m := by
    have hc := Nat.ceil_lt_add_one (pow_nonneg hl.le m)
    have hp := one_le_pow₀ hN (n := m)
    change (cutoff m N:ℝ) < Real.log (N:ℝ)^m+1 at hc
    linarith
  have htwo : (2:ℝ)^(delta m) ≤ 2 := by
    calc
      _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := Real.rpow_one _
  have hexp : (m:ℝ)*delta m = 1/2 := by
    have hm0 : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    unfold delta
    field_simp
  have hp : (Real.log (N:ℝ)^m)^(delta m) = Real.sqrt (Real.log (N:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hl.le,hexp,Real.sqrt_eq_rpow]
  calc
    _ ≤ (2*Real.log (N:ℝ)^m)^(delta m) := Real.rpow_le_rpow (Nat.cast_nonneg _) hh hd0.le
    _ = (2:ℝ)^(delta m)*(Real.log (N:ℝ)^m)^(delta m) := Real.mul_rpow (by norm_num) (pow_nonneg hl.le m)
    _ ≤ 2*Real.sqrt (Real.log (N:ℝ)) := by
      rw [hp]
      exact mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg _)

lemma log_tendsto : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma cutoff_power_log_tendsto_zero {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => (cutoff m N:ℝ)^(delta m)/Real.log (N:ℝ)) atTop (𝓝 0) := by
  have hs := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp log_tendsto)
  have hu : Tendsto (fun N : ℕ => 2*Real.sqrt (Real.log (N:ℝ))/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,Real.sqrt_div_self,mul_zero] using hs.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => div_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.log_natCast_nonneg N)
  · filter_upwards [log_tendsto.eventually (eventually_ge_atTop 1)] with N hN
    exact div_le_div_of_nonneg_right (cutoff_power_bound hm hN) (Real.log_natCast_nonneg N)

lemma eventually_smooth_count_bound {m : ℕ} (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      (((Finset.range N).filter (fun n => P n ≤ cutoff m N)).card:ℝ) ≤
        1+(N:ℝ)/(N:ℝ)^(delta m/2) := by
  obtain ⟨hd0,hd1⟩ := delta_bounds hm
  have hs := (cutoff_power_log_tendsto_zero hm).eventually_le_const
    (by positivity : (0:ℝ) < (delta m)^2/2)
  filter_upwards [hs,eventually_gt_atTop 1] with N hsN hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hexp : (cutoff m N:ℝ)^(delta m)/(delta m) ≤ (delta m/2)*Real.log (N:ℝ) := by
    have h := (div_le_iff₀ hl).mp hsN
    apply (div_le_iff₀ hd0).mpr
    nlinarith
  have hh := smooth_count_rankin_bound (σ := 1-delta m) (by linarith) (by linarith) (cutoff m N) N
  simp only [sub_sub_cancel] at hh
  calc
    _ ≤ 1+(N:ℝ)^(1-delta m)*Real.exp ((cutoff m N:ℝ)^(delta m)/(delta m)) := hh
    _ ≤ 1+(N:ℝ)^(1-delta m)*Real.exp ((delta m/2)*Real.log (N:ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (Real.rpow_nonneg hn.le _))
    _ = 1+(N:ℝ)/(N:ℝ)^(delta m/2) := by
      rw [mul_comm (delta m/2),← Real.rpow_def_of_pos hn,← Real.rpow_add hn]
      have he : 1-delta m+delta m/2 = 1-delta m/2 := by ring
      rw [he,Real.rpow_sub hn,Real.rpow_one]

lemma normalized_energy_bound (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, energy N*Real.log (N:ℝ)^B/(N:ℝ)^2 ≤
      Real.log (N:ℝ)^B/N + Real.log (N:ℝ)^B/(N:ℝ)^(delta (B+1)/2) + 1/Real.log (N:ℝ) := by
  filter_upwards [eventually_smooth_count_bound (m := B+1) (by omega),eventually_gt_atTop 1]
    with N hs hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hk := cutoff_pos (m := B+1) hN
  have hk' : (0:ℝ) < cutoff (B+1) N := Nat.cast_pos.mpr hk
  have hr : (0:ℝ) < (N:ℝ)^(delta (B+1)/2) := Real.rpow_pos_of_pos hn _
  have he : energy N ≤ (1+(N:ℝ)/(N:ℝ)^(delta (B+1)/2)+(N:ℝ)/(cutoff (B+1) N))*N := by
    exact (energy_cutoff_bound hk N).trans (mul_le_mul_of_nonneg_right
      (add_le_add hs le_rfl) hn.le)
  have hc : Real.log (N:ℝ)^B/(cutoff (B+1) N) ≤ 1/Real.log (N:ℝ) := by
    calc
      _ ≤ Real.log (N:ℝ)^B/(Real.log (N:ℝ)^(B+1)) :=
        div_le_div_of_nonneg_left (pow_nonneg hl.le B) (pow_pos hl _) (Nat.le_ceil _)
      _ = _ := by rw [pow_succ]; field_simp
  calc
    _ ≤ ((1+(N:ℝ)/(N:ℝ)^(delta (B+1)/2)+(N:ℝ)/(cutoff (B+1) N))*N)*Real.log (N:ℝ)^B/(N:ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (pow_nonneg hl.le B)) (sq_nonneg _)
    _ = Real.log (N:ℝ)^B/N + Real.log (N:ℝ)^B/(N:ℝ)^(delta (B+1)/2) +
        Real.log (N:ℝ)^B/(cutoff (B+1) N) := by field_simp
    _ ≤ _ := add_le_add le_rfl hc

/-- For every fixed `B`, the full energy saves `(log N)^B` over `N²`.
This is weaker than any fixed power saving, and does not settle Erdős 371. -/
theorem energy_log_pow_div_sq_tendsto_zero (B : ℕ) :
    Tendsto (fun N : ℕ => energy N*Real.log (N:ℝ)^B/(N:ℝ)^2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log (N:ℝ)^B/(N:ℝ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 B (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun N : ℕ => Real.log (N:ℝ)^B/(N:ℝ)^(delta (B+1)/2)) atTop (𝓝 0) := by
    have hd := (delta_bounds (show 0 < B+1 by omega)).1
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (B:ℝ) (show 0 < delta (B+1)/2 by positivity)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have h3 : Tendsto (fun N : ℕ => 1/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp log_tendsto
  have hu := (h1.add h2).add h3
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => div_nonneg
      (mul_nonneg (energy_nonneg N) (pow_nonneg (Real.log_natCast_nonneg N) B)) (sq_nonneg _)
  · exact normalized_energy_bound B

end Erdos371LogSavingEnergy

#print axioms Erdos371LogSavingEnergy.energy_log_pow_div_sq_tendsto_zero
