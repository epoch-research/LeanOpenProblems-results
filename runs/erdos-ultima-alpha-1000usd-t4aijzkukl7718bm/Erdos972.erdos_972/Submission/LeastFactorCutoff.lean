import Submission.LeastFactorSieve
import Submission.PrimeRoughOutputs

/-! A logarithmic layering cutoff within the previously verified divisor
row range. All cutoff inequalities retain their integer rounding. -/
namespace Erdos972LeastFactorCutoff

open Filter

set_option maxHeartbeats 3000000
set_option exponentiation.threshold 8192
open Erdos972LeastFactorSieve Erdos972PolynomialRowScales Erdos972PrimeRotation
open Erdos972PrimePowerError

/-- Select a doubly-exponential cutoff just below a fourth root of the
available divisor level. -/
def layerCount (u : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 (Nat.sqrt (Nat.sqrt (root64 u))))

def layerCutoff (u : ℕ) : ℕ := logLevel (layerCount u)

lemma nat_log_two_tendsto : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (2^B)] with n hn
  apply (Nat.le_log_iff_pow_le (by norm_num) (Nat.ne_of_gt ((Nat.pow_pos (by norm_num : 0 < 2)).trans_le hn))).mpr hn

lemma nat_fourth_root_tendsto :
    Tendsto (fun n : ℕ => Nat.sqrt (Nat.sqrt n)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (B^4)] with n hn
  exact (le_fourth_root_iff B n).mpr hn

lemma layerCount_tendsto : Tendsto layerCount atTop atTop :=
  nat_log_two_tendsto.comp (nat_log_two_tendsto.comp
    (nat_fourth_root_tendsto.comp root64_tendsto))

lemma logLevel_tendsto : Tendsto logLevel atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop B] with j hj
  have h₁ : j < 2^j := Nat.lt_two_pow_self
  have h₂ : 2^j < 2^(2^j) := Nat.lt_two_pow_self
  exact hj.trans (h₁.le.trans h₂.le)

lemma layerCutoff_tendsto : Tendsto layerCutoff atTop atTop :=
  logLevel_tendsto.comp layerCount_tendsto

lemma log_level_rounding {W : ℕ} (hW : 2 ≤ W) :
    logLevel (Nat.log 2 (Nat.log 2 W)) ≤ W ∧
      W < (logLevel (Nat.log 2 (Nat.log 2 W)))^2 := by
  let J := Nat.log 2 (Nat.log 2 W)
  have hlog : 0 < Nat.log 2 W := Nat.log_pos (by norm_num) hW
  have hlo : 2^J ≤ Nat.log 2 W := Nat.pow_log_le_self 2 hlog.ne'
  have hhi : Nat.log 2 W < 2^(J+1) := Nat.lt_pow_succ_log_self (by norm_num) _
  constructor
  · exact (Nat.pow_le_pow_right (by norm_num) hlo).trans
      (Nat.pow_log_le_self 2 (show W ≠ 0 by omega))
  · have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) W
    apply hh.trans_le
    have he : (logLevel J)^2 = 2^(2^(J+1)) := by
      unfold logLevel
      rw [← pow_mul, pow_succ]
    rw [← show J = Nat.log 2 (Nat.log 2 W) from rfl, he]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma layerCutoff_bounds {u : ℕ} (hu : 0 < u)
    (hW : 2 ≤ Nat.sqrt (Nat.sqrt (root64 u))) :
    (layerCutoff u)^4 ≤ root64 u ∧ u ≤ (layerCutoff u)^832 := by
  let v := root64 u
  let W := Nat.sqrt (Nat.sqrt v)
  let Z := layerCutoff u
  have hZ : 2 ≤ Z := logLevel_two_le _
  have hr := log_level_rounding hW
  change Z ≤ W ∧ W < Z^2 at hr
  obtain ⟨hv0, hvpow, huv⟩ := root64_bounds hu
  obtain ⟨hW0, hWpow, hvW⟩ := fourth_root_bounds hv0
  change W^4 ≤ v at hWpow
  change v ≤ 16*W^4 at hvW
  have hZpow : Z^4 ≤ v := (Nat.pow_le_pow_left hr.1 4).trans hWpow
  refine ⟨hZpow, ?_⟩
  have hvZ : v ≤ Z^12 := by
    calc
      v ≤ 16*W^4 := hvW
      _ ≤ (Z^4)*(Z^2)^4 := Nat.mul_le_mul (by
        simpa using Nat.pow_le_pow_left hZ 4) (Nat.pow_le_pow_left hr.2.le 4)
      _ = Z^12 := by ring
  calc
    u ≤ 2^64*v^64 := huv
    _ ≤ Z^64*(Z^12)^64 := Nat.mul_le_mul (Nat.pow_le_pow_left hZ 64)
      (Nat.pow_le_pow_left hvZ 64)
    _ = Z^832 := by ring

lemma floor_output_layer_bound {α : ℝ} {u n : ℕ} (hu : 0 < u)
    (hW : 2 ≤ Nat.sqrt (Nat.sqrt (root64 u)))
    (hα : α ≤ layerCutoff u) (hn : n ≤ u^6) :
    floorMul α n ≤ (layerCutoff u)^4993 := by
  have ho : floorMul α n ≤ layerCutoff u*n := by
    unfold floorMul
    have hh := Nat.floor_mono (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) n))
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using hh
  have hp : u^6 ≤ (layerCutoff u)^4992 := by
    have hh := Nat.pow_le_pow_left (layerCutoff_bounds hu hW).2 6
    simpa only [← pow_mul] using hh
  calc
    _ ≤ layerCutoff u*n := ho
    _ ≤ layerCutoff u*(layerCutoff u)^4992 := Nat.mul_le_mul_left _ (hn.trans hp)
    _ = _ := by rw [← pow_succ']

lemma nat_log_two_le_twice_log (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ 2*Real.log n := by
  have hh := Real.natLog_le_logb n 2
  rw [Real.logb] at hh
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hp : 0 < Real.log 2 := by linarith only [hlog2]
  have hn : 0 ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  norm_num only [Nat.cast_ofNat] at hh
  have hb := (le_div_iff₀ hp).mp hh
  have hm := mul_le_mul_of_nonneg_left hlog2 hn
  nlinarith only [hb, hm]

/-- The number of layers grows at most logarithmically in the input
logarithm. No numerical approximation to a cutoff is used. -/
lemma layerCount_loglog_bound (u : ℕ) :
    (layerCount u : ℝ) ≤ 2+2*Real.log (1+Real.log u) := by
  let W := Nat.sqrt (Nat.sqrt (root64 u))
  let H := Nat.log 2 W
  have hWle : W ≤ u := (Nat.sqrt_le_self _).trans
    ((Nat.sqrt_le_self _).trans (Erdos972GrowingCoprimeCandidates.root64_le_self u))
  have hH : (H:ℝ) ≤ 2*(1+Real.log u) := by
    have hh := nat_log_two_le_twice_log W
    have hl := Erdos972ExponentialSum.monotone_log_natCast hWle
    change (H:ℝ) ≤ 2*Real.log W at hh
    linarith only [hh, hl]
  have hL : 0 ≤ Real.log u := Real.log_natCast_nonneg u
  have hL1 : 0 < 1+Real.log u := by linarith only [hL]
  by_cases hH0 : H = 0
  · have hJ : layerCount u = 0 := by change Nat.log 2 H = 0; rw [hH0]; rfl
    rw [hJ, Nat.cast_zero]
    have hh : 0 ≤ Real.log (1+Real.log u) := Real.log_nonneg (by linarith only [hL])
    linarith only [hh]
  · have hh := nat_log_two_le_twice_log H
    change (layerCount u:ℝ) ≤ 2*Real.log H at hh
    have hlo := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hH0)) hH
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hL1.ne'] at hlo
    have htwo : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hh, hlo, htwo]

#print axioms layerCount_tendsto
#print axioms layerCutoff_bounds
#print axioms floor_output_layer_bound
#print axioms layerCount_loglog_bound

end Erdos972LeastFactorCutoff
