import Submission.RankinSmoothBound

/-! Arbitrary logarithmic savings in the unconditional, quadratic-scale
prime-winner energy bound. No near-linear energy estimate is asserted. -/

namespace Erdos371
open Finset Filter
open scoped Topology

lemma log_nat_pow_div_rpow_tendsto_zero (k : ℕ) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun N : ℕ => (Real.log N)^k / (N : ℝ)^r) atTop (nhds 0) := by
  simpa only [Real.rpow_natCast, Function.comp_apply] using
    (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

lemma polylog_smooth_ratio_power_bound (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      (((range N).filter (fun n => Nat.maxPrimeFac n ≤ polylogSmoothCutoff k N)).card : ℝ) / N ≤
        1/(N : ℝ) + 1/(N : ℝ)^δ := by
  obtain ⟨δ, hd, _, he⟩ := smooth_polylog_power_bound k
  refine ⟨δ, hd, ?_⟩
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N he hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (N : ℝ)^(1-δ) / N = 1/(N : ℝ)^δ := by
    rw [Real.rpow_sub hn0, Real.rpow_one]
    field_simp
  have h := div_le_div_of_nonneg_right he hn0.le
  rwa [add_div, hh] at h

lemma log_pow_div_polylog_cutoff (k N : ℕ) (hL : 0 < Real.log (N : ℝ)) :
    (Real.log N)^k / (polylogSmoothCutoff (k+1) N + 1 : ℝ) ≤ 1/Real.log N := by
  have hfloor := (Nat.lt_floor_add_one ((Real.log N)^(k+1))).le
  have hc : (Real.log N)^(k+1) ≤ (polylogSmoothCutoff (k+1) N + 1 : ℝ) := hfloor
  calc
    _ ≤ (Real.log N)^k / (Real.log N)^(k+1) :=
      div_le_div_of_nonneg_left (pow_nonneg hL.le k) (pow_pos hL _) hc
    _ = _ := by rw [pow_succ]; field_simp

/-- Every fixed power of log N can be saved from the elementary N^2 energy
scale. This still does not imply the N^(1+eta) estimate sufficient for the
conjecture. The proof uses only the sparsity of smooth integers and groups. -/
theorem primeWinnerEnergy_log_saving (k : ℕ) :
    Tendsto (fun N : ℕ => (Real.log N)^k * primeWinnerEnergy N / (N : ℝ)^2)
      atTop (nhds 0) := by
  obtain ⟨δ, hd, he⟩ := polylog_smooth_ratio_power_bound (k+1)
  have h1 : Tendsto (fun N : ℕ => (Real.log N)^k / (N : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using log_nat_pow_div_rpow_tendsto_zero k 1 (by norm_num)
  have hδ := log_nat_pow_div_rpow_tendsto_zero k δ hd
  have hδ' : Tendsto (fun N : ℕ => 1/(N : ℝ)^δ) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun N : ℕ => 2/Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have ht := (((h1.add hδ).mul (tendsto_one_div_atTop_nhds_zero_nat.add hδ')).add hlog).add h1
  simp only [add_zero, zero_mul] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hln : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    unfold primeWinnerEnergy
    positivity
  · filter_upwards [he, eventually_gt_atTop (1 : ℕ)] with N he hN
    have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    let B := polylogSmoothCutoff (k+1) N
    let r : ℝ := (((range N).filter (fun n => Nat.maxPrimeFac n ≤ B)).card : ℝ) / N
    let W : ℝ := (Real.log N)^k
    let M : ℝ := 1/(N : ℝ) + 1/(N : ℝ)^δ
    have hW : 0 ≤ W := pow_nonneg hln.le k
    have hr0 : 0 ≤ r := by dsimp [r]; positivity
    have hrM : r ≤ M := he
    have hsq : W*r^2 ≤ W*M^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrM 2) hW
    have hB := log_pow_div_polylog_cutoff k N hln
    have hbound := mul_le_mul_of_nonneg_left
      (primeWinnerEnergy_bulk_ratio_upper B N (by omega)) hW
    change W * (primeWinnerEnergy N / (N : ℝ)^2) ≤
      W * (r^2 + 2/(B+1 : ℝ) + 1/N) at hbound
    have hB' : W*(2/(B+1 : ℝ)) ≤ 2/Real.log N := by
      change W/(B+1 : ℝ) ≤ 1/Real.log N at hB
      convert mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
    have hM : W*M^2 =
        ((Real.log N)^k/N + (Real.log N)^k/(N : ℝ)^δ) *
          (1/(N : ℝ)+1/(N : ℝ)^δ) := by dsimp [M,W]; ring
    have hmain : W * primeWinnerEnergy N / (N : ℝ)^2 ≤
        W*M^2 + 2/Real.log N + W/N := by
      calc
        _ ≤ W * (r^2 + 2/(B+1 : ℝ) + 1/N) := by simpa only [mul_div_assoc] using hbound
        _ = W*r^2 + W*(2/(B+1 : ℝ)) + W/N := by ring
        _ ≤ _ := by gcongr
    rw [hM] at hmain
    exact hmain

#print axioms primeWinnerEnergy_log_saving
end Erdos371
