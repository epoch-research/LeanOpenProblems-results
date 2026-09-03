import Submission.SharperLinearExposure

/-! Extracting arbitrary power envelopes below the reciprocal of the verified
Buchstab exponent. The logarithmic loss is absorbed asymptotically rather
than rounded to a whole power. This does not assert a quadratic bound. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1000000

lemma log_power_add_two_le (t a : ℕ) (ht : 2 ≤ t) :
    log (((t^a : ℕ) : ℝ)+2) ≤ ((a : ℝ)+2)*log (t : ℝ) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hpow : (1 : ℝ) ≤ (t : ℝ)^a := one_le_pow₀ ht1
  have hh := log_le_log (by positivity : (0 : ℝ) < ((t^a : ℕ) : ℝ)+2)
    (show ((t^a : ℕ) : ℝ)+2 ≤ 4*(t : ℝ)^a by push_cast; linarith)
  rw [log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ ht0.ne'), log_pow] at hh
  have h4 : log (4 : ℝ) ≤ 2*log (t : ℝ) := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 4)
      (show (4 : ℝ) ≤ (t : ℝ)^2 by
        have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
        nlinarith)
    simpa only [log_pow, Nat.cast_ofNat] using h
  nlinarith only [hh,h4]

lemma log_power_add_two_rpow_le (t a : ℕ) (ht : 2 ≤ t) :
    log (((t^a : ℕ) : ℝ)+2)^(26/25 : ℝ) ≤ ((a : ℝ)+2)^2*log (t : ℝ)^2 := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hl : 0 ≤ log (((t^a : ℕ) : ℝ)+2) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (t^a); linarith)
  have hlog2 : (1/2 : ℝ) ≤ log (t : ℝ) := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ t by exact_mod_cast ht)
    linarith only [hh,log_two_gt_d9]
  have hbase : (1 : ℝ) ≤ ((a : ℝ)+2)*log (t : ℝ) := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) a,hlog2]
  have hh := rpow_le_rpow hl (log_power_add_two_le t a ht)
    (by norm_num : (0 : ℝ) ≤ 26/25)
  have he := rpow_le_rpow_of_exponent_le hbase (by norm_num : (26/25 : ℝ) ≤ 2)
  simpa only [rpow_two,mul_pow] using hh.trans he

/-- For a*(51/25)<b, a sufficiently large envelope t^b dominates the
Jacobsthal bound at t^a, including the fixed factor 2^b. -/
theorem eventually_smooth_power_envelope (C : ℝ) (hC : 0 < C)
    (hbound : ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(26/25 : ℝ))
    (a b : ℕ) (ha : 0 < a) (hab : (a : ℝ)*(51/25) < b) :
    ∀ᶠ t : ℕ in atTop,
      (jacobsthalFunction (t^a) : ℝ) ≤ (t : ℝ)^b/(2 : ℝ)^b := by
  let K : ℝ := C*((a : ℝ)+2)^2*(2 : ℝ)^b
  have hK : 0 < K := by dsimp [K]; positivity
  have hβ : 0 < (b : ℝ)-(a : ℝ)*(51/25) := sub_pos.mpr hab
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop 2 hβ).def (inv_pos.mpr hK))
  filter_upwards [hs,eventually_ge_atTop 2] with t hs ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 0 ≤ log (t : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  have hs' : log (t : ℝ)^2 ≤ (t : ℝ)^((b : ℝ)-(a : ℝ)*(51/25))/K := by
    simpa only [rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (log (t : ℝ))),
      abs_of_pos (rpow_pos_of_pos ht0 _),inv_mul_eq_div] using hs
  have hp : (((t^a : ℕ) : ℝ))^(51/25 : ℝ) = (t : ℝ)^((a : ℝ)*(51/25)) := by
    rw [Nat.cast_pow,← rpow_natCast (t : ℝ) a,← rpow_mul ht0.le]
  have hj := hbound (t^a) (Nat.pow_pos (by omega))
  have hh := mul_le_mul_of_nonneg_left (log_power_add_two_rpow_le t a ht)
    (show 0 ≤ C*(((t^a : ℕ) : ℝ))^(51/25 : ℝ) by positivity)
  have hu : (jacobsthalFunction (t^a) : ℝ) ≤
      C*((a : ℝ)+2)^2*(t : ℝ)^((a : ℝ)*(51/25))*log (t : ℝ)^2 := by
    rw [hp] at hh hj
    exact hj.trans (by convert hh using 1 <;> ring)
  have hm := mul_le_mul_of_nonneg_left hs'
    (show 0 ≤ C*((a : ℝ)+2)^2*(t : ℝ)^((a : ℝ)*(51/25)) by positivity)
  apply hu.trans
  apply hm.trans_eq
  have he : (t : ℝ)^((a : ℝ)*(51/25)) *
      (t : ℝ)^((b : ℝ)-(a : ℝ)*(51/25)) = (t : ℝ)^b := by
    rw [← rpow_add ht0, show (a : ℝ)*(51/25)+((b : ℝ)-(a : ℝ)*(51/25)) = b by ring,
      rpow_natCast]
  calc
    _ = C*((a : ℝ)+2)^2*((t : ℝ)^((a : ℝ)*(51/25)) *
          (t : ℝ)^((b : ℝ)-(a : ℝ)*(51/25)))/K := by ring
    _ = C*((a : ℝ)+2)^2*(t : ℝ)^b/K := by rw [he]
    _ = _ := by
      dsimp only [K]
      field_simp [hC.ne', show (a : ℝ)+2 ≠ 0 by positivity]

/-- The power envelope supplies an unconditional exposure budget, uniformly
in every interval length that is at least t^b/2^b. -/
theorem eventually_power_exposure_budget (a b : ℕ) (ha : 0 < a)
    (hab : (a : ℝ)*(51/25) < b) :
    ∀ᶠ t : ℕ in atTop, ∀ k : ℕ, t^b ≤ 2^b*k →
      IsJacobsthalBound (t^a-1) k := by
  obtain ⟨C,hC,hbound⟩ := RecursiveSieve.Buchstab.exists_smoothBuchstab_bound
  filter_upwards [eventually_smooth_power_envelope C hC hbound a b ha hab] with t ht
  intro k hk
  have hkR : (t : ℝ)^b ≤ (2 : ℝ)^b*k := by exact_mod_cast hk
  have hle : (jacobsthalFunction (t^a) : ℝ) ≤ k := ht.trans
    ((div_le_iff₀ (by positivity : (0 : ℝ) < 2^b)).mpr (by simpa only [mul_comm] using hkR))
  have hb := (jacobsthalFunction_le_iff (t^a) k).mp (by exact_mod_cast hle)
  intro n hn hnk r
  exact hb n hn (hnk.trans (Nat.sub_le _ _)) r

#print axioms eventually_power_exposure_budget
end Erdos970.GapAverages
