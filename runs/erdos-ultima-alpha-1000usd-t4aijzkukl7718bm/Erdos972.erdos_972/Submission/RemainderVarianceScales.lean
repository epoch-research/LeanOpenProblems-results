import Submission.RemainderVariance
import Submission.CovarianceScaleBudgets

/-! A concrete obstruction to proving sublinear variance for the signed
Vaughan remainder at the cutoffs used in the four-factor reduction. -/
namespace Erdos972RemainderVarianceScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972RemainderVariance Erdos972PrimeIntervalCounts Erdos972RemainderSemiprimes
open Erdos972DoubleVaughan Erdos972LogarithmicCovariance
open Erdos972GrowingTypeIIReduction Erdos972PolynomialRowScales
open Erdos972CenteredRowScales Erdos972CovarianceScaleBudgets Erdos972ExponentialSum

set_option maxHeartbeats 1000000

lemma growingCutoff_power (u : ℕ) : (growingCutoff u)^128 ≤ u := by
  have hh := Nat.pow_le_pow_left (growingCutoff_eligible u).2 64
  have he : (growingCutoff u*growingCutoff u)^64 = (growingCutoff u)^128 := by ring
  rw [he] at hh
  exact hh.trans ((le_root64_iff (root64 u) u).mp le_rfl)

lemma growingCutoff_main_power {α : ℝ} (hα : 1 ≤ α) {u : ℕ} (hu : 0 < u) (hαu : 2*α ≤ u) :
    (growingCutoff u)^640 ≤ scaleCutoff α u := by
  have hαu' : α ≤ u := by linarith only [hα, hαu]
  have hscale := (scaleCutoff_bounds hα hu hαu').2.2
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hh := mul_le_mul_of_nonneg_right hαu (Nat.cast_nonneg (α := ℝ) (scaleCutoff α u))
  have hfive : u^5 ≤ scaleCutoff α u := by
    have hh' : (u : ℝ)*(u : ℝ)^5 ≤ (u : ℝ)*scaleCutoff α u := by nlinarith only [hscale, hh]
    have hh'' : (u : ℝ)^5 ≤ scaleCutoff α u := (mul_le_mul_iff_right₀ huR).mp hh'
    exact_mod_cast hh''
  have hW := Nat.pow_le_pow_left (growingCutoff_power u) 5
  have he : ((growingCutoff u)^128)^5 = (growingCutoff u)^640 := by ring
  rw [he] at hW
  exact hW.trans hfive

noncomputable def cofactorCutoff (α : ℝ) (u : ℕ) := scaleCutoff α u/(4*growingCutoff u)

lemma cofactor_ge_square {N W : ℕ} (hW : 4 ≤ W) (hWN : W^640 ≤ N) : W^2 ≤ N/(4*W) := by
  have hW0 : 0 < W := by omega
  apply (Nat.le_div_iff_mul_le (show 0 < 4*W by positivity)).mpr
  have hp : W^4 ≤ W^640 := Nat.pow_le_pow_right hW0 (by norm_num)
  have hh := Nat.mul_le_mul_right (W^3) hW
  nlinarith only [hh, hp, hWN]

lemma cofactorCutoff_tendsto {α : ℝ} (hα : 1 ≤ α) : Tendsto (cofactorCutoff α) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [growingCutoff_tendsto.eventually_ge_atTop (max B 4),
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈2*α⌉₊] with u hW hu huα
  have hαu : 2*α ≤ u := (Nat.le_ceil _).trans (Nat.cast_le.mpr huα)
  have hpow := growingCutoff_main_power hα hu hαu
  have hQ := cofactor_ge_square ((le_max_right B 4).trans hW) hpow
  have hW2 : growingCutoff u ≤ (growingCutoff u)^2 := Nat.le_self_pow (by norm_num) _
  exact ((le_max_left B 4).trans hW).trans (hW2.trans hQ)

lemma logarithmic_separation {N W : ℕ} (hW : 512 ≤ W) (hWN : W^640 ≤ N) :
    576*Real.log (2*W : ℕ) ≤ Real.log N := by
  have hW0 : 0 < W := by omega
  have hh := monotone_log_natCast (show 2^9 ≤ W by norm_num at *; exact hW)
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hh
  have hn := monotone_log_natCast hWN
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hn
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hW0))]
  nlinarith only [hh, hn]

/-- The actual remainder does not have sublinear variance. In fact its
variance is eventually strictly larger than N at the exact power-growing
cutoffs of the centered four-factor reduction. -/
theorem eventually_remainder_variance_lower {α : ℝ} (hα : 1 ≤ α) :
    ∀ᶠ u : ℕ in atTop, (9/8 : ℝ)*(scaleCutoff α u : ℝ) ≤
      covariance (scaleCutoff α u) (fun n => typeIIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIIPart (growingCutoff u) (growingCutoff u) n) := by
  have hlogW := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp growingCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [growingCutoff_tendsto.eventually_ge_atTop 512,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈2*α⌉₊, hlogW,
    growingCutoff_tendsto.eventually eventually_prime_interval_counts,
    (cofactorCutoff_tendsto hα).eventually eventually_prime_interval_counts,
    (scaleCutoff_tendsto hα).eventually eventually_prime_interval_counts] with u hW hu huα hlogW hcountW hcountQ hcountN
  have hαu : 2*α ≤ u := (Nat.le_ceil _).trans (Nat.cast_le.mpr huα)
  have hpow := growingCutoff_main_power hα hu hαu
  let W := growingCutoff u
  let N := scaleCutoff α u
  let Q := cofactorCutoff α u
  have hW0 : 0 < W := by dsimp [W]; omega
  have hN : 0 < N := by dsimp [N]; omega
  have hQsq : W^2 ≤ Q := cofactor_ge_square (by dsimp [W]; omega) hpow
  have hsep : 2*W < Q := by
    have hW4 : 4 ≤ W := by dsimp [W]; omega
    nlinarith only [hW4, hQsq]
  have hQ : 0 < Q := by omega
  have hprod : 4*W*Q ≤ N := Nat.mul_div_le N (4*W)
  have hcover : N ≤ 8*W*Q := by
    have hh := Nat.lt_mul_div_succ N (show 0 < 4*W by positivity)
    change N < (4*W)*(Q+1) at hh
    have hmul := Nat.mul_le_mul_left (4*W) (show Q+1 ≤ 2*Q by omega)
    nlinarith only [hh, hmul]
  have hlogW' : 1 ≤ Real.log (2*W : ℕ) := hlogW.trans (monotone_log_natCast (by omega : W ≤ 2*W))
  have hsepLog : 576*Real.log (2*W : ℕ) ≤ Real.log N := logarithmic_separation hW hpow
  have hlogN : 2*Real.log 8 ≤ Real.log N := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    nlinarith only [hlogW', hsepLog, hh]
  have hb := remainder_variance_lower hW0 hN hsep hprod hcover hlogW' hlogN hcountN.2.1 hcountW.2.2 hcountQ.2.2
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlogW0 : 0 < Real.log (2*W : ℕ) := by linarith only [hlogW']
  have hlarge : (9/8 : ℝ)*N ≤ (N : ℝ)*Real.log N/(512*Real.log (2*W : ℕ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 512*Real.log (2*W : ℕ))).mpr
    have hh := mul_le_mul_of_nonneg_left hsepLog hNR.le
    nlinarith only [hh]
  exact hlarge.trans hb

theorem eventually_remainder_variance_gt_main {α : ℝ} (hα : 1 ≤ α) :
    ∀ᶠ u : ℕ in atTop, (scaleCutoff α u : ℝ) <
      covariance (scaleCutoff α u) (fun n => typeIIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIIPart (growingCutoff u) (growingCutoff u) n) := by
  filter_upwards [eventually_remainder_variance_lower hα,
    (scaleCutoff_tendsto hα).eventually_ge_atTop 1] with u hv hN
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  linarith only [hv, hNR]

/-- A proposed o(N) variance estimate for this actual remainder is false. -/
theorem not_tendsto_remainder_variance_zero {α : ℝ} (hα : 1 ≤ α) :
    ¬ Tendsto (fun u : ℕ =>
      covariance (scaleCutoff α u) (fun n => typeIIPart (growingCutoff u) (growingCutoff u) n)
        (fun n => typeIIPart (growingCutoff u) (growingCutoff u) n)/(scaleCutoff α u : ℝ))
      atTop (𝓝 0) := by
  intro hlim
  obtain ⟨u, hu, hv, hN⟩ := ((tendsto_order.mp hlim).2 1 (by norm_num)).and
    ((eventually_remainder_variance_gt_main hα).and ((scaleCutoff_tendsto hα).eventually_ge_atTop 1)) |>.exists
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hh := (div_lt_iff₀ hNR).mp hu
  linarith only [hh, hv]

#print axioms eventually_remainder_variance_lower
#print axioms eventually_remainder_variance_gt_main
#print axioms not_tendsto_remainder_variance_zero

end Erdos972RemainderVarianceScales
