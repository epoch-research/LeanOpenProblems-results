import Submission.BuchstabPolylogarithmicGrowth
import Submission.ArbitrarySubcriticalExposure

/-! Exposure sizes at the square-root scale with a fixed logarithmic loss.
The Jacobsthal bound used here retains its fixed log power. No quadratic
endpoint estimate is asserted. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1600000

lemma eventually_log_nat_ge (M : ℝ) :
    ∀ᶠ t : ℕ in atTop, M ≤ log (t : ℝ) :=
  (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop M)

lemma eventually_nat_log_power_small (d a : ℕ) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, log (t : ℝ)^d ≤ ε*(t : ℝ)^a := by
  have hs := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop (d : ℝ) (by exact_mod_cast ha : (0 : ℝ) < a)).def hε)
  filter_upwards [hs,eventually_ge_atTop 1] with t ht ht1
  have hlog : 0 ≤ log (t : ℝ) := log_nonneg (by exact_mod_cast ht1)
  simpa only [rpow_natCast,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog d),abs_of_nonneg (pow_nonneg (show (0 : ℝ) ≤ t from Nat.cast_nonneg t) a)] using ht

noncomputable def logExposureSize (b t : ℕ) : ℕ :=
  ⌊(t : ℝ)^40/log (t : ℝ)^b⌋₊

lemma logExposureSize_bounds (b t : ℕ) (ht : 1 ≤ t)
    (hL : 1 ≤ log (t : ℝ))
    (hsmall : log (t : ℝ)^b ≤ (t : ℝ)^40/2) :
    0 < logExposureSize b t ∧
    (logExposureSize b t : ℝ) ≤ (t : ℝ)^40 ∧
    (logExposureSize b t : ℝ)*log (t : ℝ)^b ≤ (t : ℝ)^40 ∧
    (t : ℝ)^40/(2*log (t : ℝ)^b) ≤ logExposureSize b t := by
  have hL0 : 0 < log (t : ℝ) := by linarith
  have hpow : 0 < log (t : ℝ)^b := pow_pos hL0 _
  have hquot : 2 ≤ (t : ℝ)^40/log (t : ℝ)^b :=
    (le_div_iff₀ hpow).mpr (by linarith)
  have hfloor := Nat.floor_le (by positivity : 0 ≤ (t : ℝ)^40/log (t : ℝ)^b)
  have hfloor' := Nat.lt_floor_add_one ((t : ℝ)^40/log (t : ℝ)^b)
  have hmul := (le_div_iff₀ hpow).mp hfloor
  refine ⟨Nat.floor_pos.mpr (by linarith),?_,?_,?_⟩
  · exact hfloor.trans (div_le_self (by positivity) (one_le_pow₀ hL))
  · exact hmul
  · dsimp only [logExposureSize]
    have he : (t : ℝ)^40/(2*log (t : ℝ)^b) =
        ((t : ℝ)^40/log (t : ℝ)^b)/2 := by ring
    rw [he]
    linarith

/-- The polylogarithmic upper bound provides an inverse exposure budget.
The fixed loss exponent is one larger than the exponent in that bound. -/
lemma eventually_log_exposure_budget_of_bound (d : ℕ) (A : ℝ) (hA : 0 < A)
    (hbound : ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ A*(k : ℝ)^2*log ((k : ℝ)+2)^d) :
    ∀ᶠ t : ℕ in atTop, 0 < logExposureSize (d+1) t ∧
      ∀ k : ℕ, t^80 ≤ 2^80*k →
        IsJacobsthalBound (logExposureSize (d+1) t-1) k := by
  filter_upwards [eventually_log_nat_ge 1,
    eventually_log_nat_ge (A*42^d*2^80),
    eventually_nat_log_power_small (d+1) 40 (by omega) (1/2) (by norm_num),
    eventually_ge_atTop 2] with t hL hK hsmall ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hL0 : 0 < log (t : ℝ) := by linarith
  have hb := logExposureSize_bounds (d+1) t (by omega) hL (by linarith only [hsmall])
  let j := logExposureSize (d+1) t
  have hj : 0 < j := hb.1
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjt : (j : ℝ) ≤ (t : ℝ)^40 := hb.2.1
  have hjmul : (j : ℝ)*log (t : ℝ)^(d+1) ≤ (t : ℝ)^40 := hb.2.2.1
  have hlogj : log ((j : ℝ)+2) ≤ 42*log (t : ℝ) := by
    have hh := log_power_add_two_le t 40 ht
    norm_num only [Nat.cast_ofNat] at hh
    apply le_trans (log_le_log (by positivity) (add_le_add hjt (le_refl (2 : ℝ))))
    simpa only [Nat.cast_pow] using hh
  have hhj := hbound j hj
  have hlogpow := pow_le_pow_left₀ (log_nonneg (by linarith only [hj0] : (1 : ℝ) ≤ (j : ℝ)+2)) hlogj d
  have hupper : (jacobsthalFunction j : ℝ) ≤
      A*42^d*(j : ℝ)^2*log (t : ℝ)^d := by
    apply hhj.trans
    have hh := mul_le_mul_of_nonneg_left hlogpow (show 0 ≤ A*(j : ℝ)^2 by positivity)
    simpa only [mul_pow] using (show A*(j : ℝ)^2*(42*log (t : ℝ))^d =
      A*42^d*(j : ℝ)^2*log (t : ℝ)^d by ring_nf) ▸ hh
  have hprod := mul_le_mul hjt hjmul (by positivity : 0 ≤ (j : ℝ)*log (t : ℝ)^(d+1))
    (by positivity : 0 ≤ (t : ℝ)^40)
  have hprod' : (j : ℝ)^2*log (t : ℝ)^d*log (t : ℝ) ≤ (t : ℝ)^80 := by
    convert hprod using 1 <;> ring
  have hscale := mul_le_mul_of_nonneg_left hK
    (show 0 ≤ (j : ℝ)^2*log (t : ℝ)^d by positivity)
  have hscaled : (jacobsthalFunction j : ℝ)*2^80 ≤ (t : ℝ)^80 := by
    have hupper' := mul_le_mul_of_nonneg_right hupper (by positivity : (0 : ℝ) ≤ 2^80)
    apply hupper'.trans
    apply le_trans (by convert hscale using 1 <;> ring)
    exact hprod'
  refine ⟨hj,fun k hk => ?_⟩
  have hkR : (t : ℝ)^80 ≤ 2^80*(k : ℝ) := by exact_mod_cast hk
  have hle : (jacobsthalFunction j : ℝ) ≤ k := by
    have hh := hscaled.trans hkR
    nlinarith only [hh]
  have hB := (jacobsthalFunction_le_iff j k).mp (by exact_mod_cast hle)
  intro n hn hnj r
  exact hB n hn (hnj.trans (Nat.sub_le _ _)) r

/-- One fixed logarithmic exposure loss works for every sufficiently large
power envelope and every allowed interval length. -/
theorem exists_log_exposure_budget : ∃ b : ℕ, 0 < b ∧
    ∀ᶠ t : ℕ in atTop, 0 < logExposureSize b t ∧
      ∀ k : ℕ, t^80 ≤ 2^80*k →
        IsJacobsthalBound (logExposureSize b t-1) k := by
  obtain ⟨d,A,hA,hbound⟩ := RecursiveSieve.Buchstab.exists_quadratic_polylogarithmic_bound
  exact ⟨d+1,by omega,eventually_log_exposure_budget_of_bound d A hA hbound⟩

#print axioms exists_log_exposure_budget
end Erdos970.GapAverages
