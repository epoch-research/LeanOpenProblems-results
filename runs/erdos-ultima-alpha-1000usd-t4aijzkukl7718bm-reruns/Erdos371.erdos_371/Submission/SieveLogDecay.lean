import FormalConjecturesUtil
import Submission.SieveScaleBands

/-! An abstract logarithmic decay consequence of the explicit Brun parameters.
This upgrades the stated sieve majorant, not an arbitrary signed discrepancy. -/

namespace Erdos371SieveLogDecay

open Finset Filter Erdos371SieveParameters Erdos371SieveScaleBands
open scoped Topology

lemma coefficient_le_tail {K k : ℕ} (h : K ≤ k) : coefficient k ≤ tail K := by
  exact (Finset.single_le_sum (fun j _ => coefficient_nonneg j)
    (Finset.mem_Ico.mpr ⟨h, Nat.lt_succ_self k⟩)).trans (coefficient_sum_le_tail K (k+1))

lemma cutoff_sq_le_threshold (k : ℕ) : cutoff k ^ 2 ≤ threshold k := by
  apply Nat.pow_le_pow_right (by have := cutoff_two_le k; omega)
  have := depth_pos k
  omega

lemma choose_sieve_index {K N : ℕ} (hN : threshold K ≤ N) :
    ∃ k, K ≤ k ∧ threshold k ≤ N ∧
      Real.log (N:ℝ)/(4:ℝ)^k ≤ tail K := by
  have hNp : 0 < N := (Nat.pow_pos (by norm_num : 0<(2:ℕ))).trans_le
    ((threshold_eq_pow K) ▸ hN)
  let t := Nat.log 2 N
  have htK : exponent K ≤ t := by
    apply Nat.le_log_of_pow_le (by norm_num)
    simpa only [threshold_eq_pow] using hN
  obtain ⟨k,hk,hband⟩ := exists_band (K := K) (t := t) (j := 0) (by simpa using htK)
  obtain ⟨hKk,hkt⟩ := Finset.mem_Ico.mp hk
  have hlevels := (Finset.mem_filter.mp hband).2
  simp only [mul_zero, zero_add] at hlevels
  have hpow : 2^t ≤ N := Nat.pow_log_le_self 2 hNp.ne'
  have hNk : threshold k ≤ N := by
    rw [threshold_eq_pow]
    exact (Nat.pow_le_pow_right (by norm_num) hlevels.1).trans hpow
  have hupper : N < 2^(t+1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hlog : Real.log (N:ℝ) ≤ (exponent (k+1):ℝ) := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr hNp)
      (show (N:ℝ) ≤ (2:ℝ)^(t+1) by exact_mod_cast hupper.le)
    rw [Real.log_pow] at hh
    have ht : (t+1:ℝ) ≤ exponent (k+1) := by exact_mod_cast hlevels.2
    have hl : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ (t+1:ℝ) by positivity)
    push_cast at hh
    linarith
  refine ⟨k,hKk,hNk,?_⟩
  exact (div_le_div_of_nonneg_right hlog (by positivity)).trans (coefficient_le_tail hKk)

lemma logarithmic_boundary_tendsto_zero :
    Tendsto (fun N : ℕ => (1+Real.sqrt N)*Real.log N/N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ => Real.log (N:ℝ)/Real.sqrt N) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1/2:ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have h := hlog.add hsqrt
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs : Real.sqrt (N:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  have he := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  field_simp
  linear_combination -Real.log (N:ℝ) * he

/-- A majorant with a small cutoff term and the explicit two-dimensional
sieve saving is `o(N/log N)`. No bound for an unrelated count is implicit. -/
theorem log_decay_of_sieve_bound {F : ℕ → ℝ} (hF : ∀ N, 0 ≤ F N)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k N : ℕ, 0 < N → threshold k ≤ N →
      F N ≤ C*(1+(cutoff k:ℝ)+(N:ℝ)/(4:ℝ)^k)) :
    Tendsto (fun N : ℕ => F N*Real.log N/N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K,hK⟩ := ((tail_tendsto_zero.const_mul C).eventually_lt_const
    (show C*0 < ε/2 by simpa using half_pos hε)).exists
  have hb := (logarithmic_boundary_tendsto_zero.const_mul C).eventually_lt_const
    (show C*0 < ε/2 by simpa using half_pos hε)
  filter_upwards [hb,eventually_ge_atTop (threshold K),eventually_gt_atTop 0] with N hbN hNK hN
  obtain ⟨k,hKk,hNk,hkt⟩ := choose_sieve_index hNK
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hlog := Real.log_natCast_nonneg N
  have hcut : (cutoff k:ℝ) ≤ Real.sqrt N := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast (cutoff_sq_le_threshold k).trans hNk
  have hmajor := hbound k N hN hNk
  have hmul := mul_le_mul_of_nonneg_right hmajor (div_nonneg hlog hn.le)
  have hsmall := mul_le_mul_of_nonneg_left hkt hC
  have hcutmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (show 1+(cutoff k:ℝ) ≤ 1+Real.sqrt N by linarith)
      (div_nonneg hlog hn.le)) hC
  have he : C*(1+(cutoff k:ℝ)+(N:ℝ)/(4:ℝ)^k)*(Real.log N/N) =
      C*((1+(cutoff k:ℝ))*Real.log N/N)+C*(Real.log N/(4:ℝ)^k) := by
    field_simp
  rw [he] at hmul
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (mul_nonneg (hF N) hlog) hn.le)]
  change C*tail K < ε/2 at hK
  change C*((1+Real.sqrt N)*Real.log N/N) < ε/2 at hbN
  calc
    F N*Real.log N/N = F N*(Real.log N/N) := by ring
    _ ≤ C*((1+(cutoff k:ℝ))*Real.log N/N)+C*(Real.log N/(4:ℝ)^k) := hmul
    _ ≤ C*((1+Real.sqrt N)*Real.log N/N)+C*tail K :=
      add_le_add (by simpa only [mul_div_assoc] using hcutmul) hsmall
    _ < ε := by linarith

end Erdos371SieveLogDecay

#print axioms Erdos371SieveLogDecay.log_decay_of_sieve_bound
