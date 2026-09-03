import FormalConjecturesUtil
import Submission.SubpowerCutoff

/-! A near-linear (`N^{1+o(1)}`) winning-prime energy estimate would suffice.
This file does not establish that estimate. -/

namespace Erdos371NearLinearEnergy

open Erdos371PrimeDiscrepancy Erdos371PrimeEnergy Erdos371SubpowerCutoff Filter
open scoped Topology

noncomputable def load (N : ℕ) : ℝ := 1 + energy N/N
noncomputable def cutoff (N : ℕ) : ℕ := ⌈(load N)^2 * Real.log (N:ℝ)⌉₊

lemma load_one_le (N : ℕ) : 1 ≤ load N := by
  unfold load
  exact le_add_of_nonneg_right (div_nonneg (energy_nonneg N) (Nat.cast_nonneg _))

lemma load_pos (N : ℕ) : 0 < load N := lt_of_lt_of_le zero_lt_one (load_one_le N)

lemma logN_tendsto : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma cutoff_eventually_pos : ∀ᶠ N in atTop, 0 < cutoff N := by
  filter_upwards [logN_tendsto.eventually (eventually_ge_atTop 1)] with N hN
  apply Nat.ceil_pos.mpr
  exact mul_pos (sq_pos_of_pos (load_pos N)) (by linarith)

lemma cutoff_log_bound {N : ℕ} (hN : 1 ≤ Real.log (N:ℝ)) :
    Real.log (cutoff N : ℝ) ≤ Real.log 2 + 2*Real.log (load N) + Real.log (Real.log (N:ℝ)) := by
  have hl := load_pos N
  have hlog : 0 < Real.log (N:ℝ) := by linarith
  have harg : 1 ≤ (load N)^2 * Real.log (N:ℝ) := by
    have hh : 1 ≤ (load N)^2 := by nlinarith [load_one_le N]
    nlinarith
  have hKpos : 0 < cutoff N := Nat.ceil_pos.mpr (by linarith)
  have hKbound : (cutoff N : ℝ) ≤ 2 * (load N)^2 * Real.log (N:ℝ) := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ (load N)^2 * Real.log (N:ℝ))
    change (cutoff N : ℝ) < _ at hh
    linarith
  have hh := Real.log_le_log (Nat.cast_pos.mpr hKpos) hKbound
  rw [Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 hl.ne')) hlog.ne',
    Real.log_mul (by norm_num) (pow_ne_zero 2 hl.ne'), Real.log_pow] at hh
  norm_num at hh
  exact hh

lemma cutoff_log_tendsto
    (hE : Tendsto (fun N : ℕ => Real.log (load N) / Real.log (N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (cutoff N : ℝ) / Real.log (N:ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => 1/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp logN_tendsto
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp logN_tendsto
  have hu : Tendsto (fun N : ℕ => Real.log 2 / Real.log (N:ℝ) +
      2 * (Real.log (load N) / Real.log (N:ℝ)) +
      Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using ((tendsto_const_nhds.mul hi).add (tendsto_const_nhds.mul hE)).add hll
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · filter_upwards [logN_tendsto.eventually (eventually_ge_atTop 1)] with N hN
    have hh := div_le_div_of_nonneg_right (cutoff_log_bound hN) (Real.log_natCast_nonneg N)
    simpa [add_div, mul_div_assoc] using hh

lemma cutoff_energy_tendsto_zero :
    Tendsto (fun N => energy N / ((N:ℝ)*cutoff N)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => 1/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp logN_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => div_nonneg (energy_nonneg N) (by positivity)
  · filter_upwards [logN_tendsto.eventually (eventually_ge_atTop 1)] with N hN
    have hl : 0 < Real.log (N:ℝ) := by linarith
    have hload := load_pos N
    have harg : 0 < (load N)^2 * Real.log (N:ℝ) := mul_pos (sq_pos_of_pos hload) hl
    have hK : (load N)^2 * Real.log (N:ℝ) ≤ (cutoff N : ℝ) := Nat.le_ceil _
    rw [← div_div]
    calc
      _ ≤ (energy N/(N:ℝ))/((load N)^2 * Real.log (N:ℝ)) :=
        div_le_div_of_nonneg_left (div_nonneg (energy_nonneg N) (Nat.cast_nonneg _)) harg hK
      _ ≤ (load N)^2 / ((load N)^2 * Real.log (N:ℝ)) := by
        apply div_le_div_of_nonneg_right _ harg.le
        have hh := load_one_le N
        unfold load at hh ⊢
        nlinarith
      _ = 1/Real.log (N:ℝ) := by field_simp

/-- A subpower loss over linear energy is sufficient. The hypothesis is not
an unconditional theorem about `energy`. -/
theorem density_half_of_log_energy_load
    (hE : Tendsto (fun N : ℕ => Real.log (1 + energy N/N) / Real.log (N:ℝ))
      atTop (𝓝 0)) :
    {n | P n < P (n+1)}.HasDensity (1/2) := by
  exact density_half_of_subpower_cutoff cutoff cutoff_eventually_pos
    (cutoff_log_tendsto hE) cutoff_energy_tendsto_zero


/-- In particular, an eventual `N * N^ε` bound for every positive ε suffices. -/
theorem density_half_of_subpower_energy
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, energy N ≤ (N:ℝ) * (N:ℝ)^ε) :
    {n | P n < P (n+1)}.HasDensity (1/2) := by
  apply density_half_of_log_energy_load
  change Tendsto (fun N : ℕ => Real.log (load N) / Real.log (N:ℝ)) _ _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε/2 := half_pos hε
  have hi : Tendsto (fun N : ℕ => Real.log 2 / Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp logN_tendsto)
  filter_upwards [hE (ε/2) hδ, hi.eventually_lt_const hδ, eventually_gt_atTop 1]
    with N hEN hsmall hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hp : 1 ≤ (N:ℝ)^(ε/2) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) hδ.le
  have hload : load N ≤ 2 * (N:ℝ)^(ε/2) := by
    have hh : energy N/(N:ℝ) ≤ (N:ℝ)^(ε/2) := (div_le_iff₀ hn).mpr (by nlinarith [hEN])
    unfold load
    linarith
  have hlog := Real.log_le_log (load_pos N) hload
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn (ε/2)).ne', Real.log_rpow hn] at hlog
  have hh := div_le_div_of_nonneg_right hlog hl.le
  have he : (Real.log 2 + ε/2 * Real.log (N:ℝ))/Real.log (N:ℝ) =
      Real.log 2 / Real.log (N:ℝ) + ε/2 := by field_simp
  rw [he] at hh
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (Real.log_nonneg (load_one_le N)) hl.le)]
  linarith

/-- Every fixed polylogarithmic loss over linear energy is also sufficient.
The growth estimate is an assumption, not a proved estimate for this sequence. -/
theorem density_half_of_polylog_energy (A : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ᶠ N : ℕ in atTop, energy N ≤ C*N*(Real.log (N:ℝ))^A) :
    {n | P n < P (n+1)}.HasDensity (1/2) := by
  apply density_half_of_log_energy_load
  change Tendsto (fun N : ℕ => Real.log (load N) / Real.log (N:ℝ)) _ _
  have hi : Tendsto (fun N : ℕ => 1/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp logN_tendsto
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp logN_tendsto
  have hu : Tendsto (fun N : ℕ => Real.log (1+C)/Real.log (N:ℝ) +
      A * (Real.log (Real.log (N:ℝ))/Real.log (N:ℝ))) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using (tendsto_const_nhds.mul hi).add (tendsto_const_nhds.mul hll)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => div_nonneg
      (Real.log_nonneg (load_one_le N)) (Real.log_natCast_nonneg N)
  · filter_upwards [hE, logN_tendsto.eventually (eventually_ge_atTop 1), eventually_gt_atTop 0]
      with N hEN hlog hN
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hl : 0 < Real.log (N:ℝ) := by linarith
    have hp : 1 ≤ (Real.log (N:ℝ))^A := one_le_pow₀ hlog
    have hc : 0 < 1+C := by linarith
    have hload : load N ≤ (1+C)*(Real.log (N:ℝ))^A := by
      have hh : energy N/(N:ℝ) ≤ C*(Real.log (N:ℝ))^A :=
        (div_le_iff₀ hn).mpr (by nlinarith [hEN])
      unfold load
      nlinarith
    have hh := Real.log_le_log (load_pos N) hload
    rw [Real.log_mul hc.ne' (pow_ne_zero A hl.ne'), Real.log_pow] at hh
    have hh' := div_le_div_of_nonneg_right hh hl.le
    simpa [add_div, mul_div_assoc] using hh'

end Erdos371NearLinearEnergy

#print axioms Erdos371NearLinearEnergy.density_half_of_log_energy_load

#print axioms Erdos371NearLinearEnergy.density_half_of_subpower_energy
#print axioms Erdos371NearLinearEnergy.density_half_of_polylog_energy
