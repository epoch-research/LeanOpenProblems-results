import Submission.GlobalTwoScaleMinorant
import Submission.PrimeSmoothMeanScales
import Submission.CesaroLogarithmicMean

/-! The damped global minorant has a strictly negative fixed-parameter
prime-input mean at arbitrarily large common irrational good scales.
This diagnoses a limitation of the minorant; it does not settle Erdős 972. -/
namespace Erdos972GlobalMinorantMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972GlobalTwoScaleMinorant Erdos972PrimePowerError
open Erdos972PrimeLeastFactorScales Erdos972PrimeRoughOutputs
open Erdos972PrimeSmoothMeanScales Erdos972FullSmoothL1Obstruction
open Erdos972CesaroLogarithmicMean Erdos972DampedMeanMonotonic
open Erdos972FixedDampedCorrelation Erdos972PolynomialRowScales
open Erdos972SelbergLowerTest Erdos972DivisorCovariance
open Erdos972ExponentialSum Erdos972ExactLargeDivisorFirstMoment

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma damped_minorant_identity {t : ℝ} (ht : 0 < t) (n : ℕ) :
    halfDamping t n * globalMinorant t n =
      smoothMangoldt t n / 2 - smoothMangoldt (2*t) n +
        (halfDamping t n + (halfDamping t n)^2/2)*smoothMangoldt t n := by
  by_cases hn : n = 1
  · simp [hn, globalMinorant, smoothMangoldt, expDivisorSum]
  rw [globalMinorant, if_neg hn, smoothMangoldt, smoothMangoldt,
    expDivisorSum_at_zero, one_apply, if_neg hn, sub_zero]
  have hz := (halfDamping_pos t n).ne'
  field_simp
  ring

lemma halfDamping_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    halfDamping t n ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (show 0 ≤ t/2 from div_nonneg ht (by norm_num)))
    (Real.log_natCast_nonneg n)

lemma halfDamping_floor_le {t α : ℝ} (ht : 0 ≤ t) (hα : 1 ≤ α) (n : ℕ) :
    halfDamping t (floorMul α n) ≤ halfDamping t n := by
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left
    (monotone_log_natCast (self_le_floorMul hα n)) (show 0 ≤ t/2 from div_nonneg ht (by norm_num))
  linarith only [hh]

noncomputable def correction (t α : ℝ) (n : ℕ) : ℝ :=
  primeWeight n *
    (halfDamping t (floorMul α n) + (halfDamping t (floorMul α n))^2/2) *
      smoothMangoldt t (floorMul α n)

lemma correction_nonneg {t : ℝ} (ht : 0 < t) (α : ℝ) (n : ℕ) :
    0 ≤ correction t α n := by
  unfold correction
  positivity [primeWeight_nonneg n, halfDamping_pos t (floorMul α n),
    smoothMangoldt_nonneg ht (floorMul α n)]

lemma correction_bound {t α : ℝ} (ht : 0 < t) (hα : 1 ≤ α) (n : ℕ) :
    correction t α n ≤ (3/(2*t)) * (Real.log n * halfDamping t n) := by
  have hz := (halfDamping_pos t (floorMul α n)).le
  have hz1 := halfDamping_le_one ht.le (floorMul α n)
  have hzn := halfDamping_floor_le ht.le hα n
  have hp : primeWeight n ≤ Real.log n := by
    unfold primeWeight
    split_ifs <;> simp [Real.log_natCast_nonneg]
  have hcoef : halfDamping t (floorMul α n) + (halfDamping t (floorMul α n))^2/2 ≤
      (3/2:ℝ)*halfDamping t n := by
    nlinarith only [mul_le_mul_of_nonneg_left hz1 hz, hzn]
  have hbound := mul_le_mul
    (mul_le_mul hp hcoef (by positivity) (Real.log_natCast_nonneg n))
    (smoothMangoldt_le_inv ht (floorMul α n))
    (smoothMangoldt_nonneg ht (floorMul α n)) (by positivity [Real.log_natCast_nonneg n, halfDamping_pos t n])
  exact hbound.trans_eq (by ring)

lemma log_halfDamping_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => Real.log n * halfDamping t n) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (t/2)
    (half_pos ht)).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  simpa only [Function.comp_apply, Real.rpow_one, halfDamping] using hh

lemma correction_tendsto {t α : ℝ} (ht : 0 < t) (hα : 1 ≤ α) :
    Tendsto (correction t α) atTop (𝓝 0) := by
  have hh := (log_halfDamping_tendsto ht).const_mul (3/(2*t))
  simp only [mul_zero] at hh
  exact squeeze_zero (correction_nonneg ht α) (correction_bound ht hα) hh

noncomputable def correctionMean (t α : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Ioc 0 N, correction t α n)/(N:ℝ)

lemma correctionMean_nonneg {t : ℝ} (ht : 0 < t) (α : ℝ) (N : ℕ) :
    0 ≤ correctionMean t α N :=
  div_nonneg (sum_nonneg (fun n _ => correction_nonneg ht α n)) (Nat.cast_nonneg N)

lemma correctionMean_tendsto {t α : ℝ} (ht : 0 < t) (hα : 1 ≤ α) :
    Tendsto (correctionMean t α) atTop (𝓝 0) := by
  have hh := weighted_mean ((tendsto_add_atTop_iff_nat 1).mpr (correction_tendsto ht hα))
    (w := fun _ => (1:ℝ)) (fun _ => zero_le_one)
    (by simpa using (tendsto_natCast_atTop_atTop (R := ℝ)))
  change Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, correction t α n)/(N:ℝ)) atTop (𝓝 0)
  simpa only [sum_Ioc_eq_sum_range_succ, mul_one, sum_const,
    card_range, nsmul_eq_mul] using hh

noncomputable def dampedGlobalMean (t α : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Ioc 0 N, primeWeight n * halfDamping t (floorMul α n) *
    globalMinorant t (floorMul α n))/(N:ℝ)

lemma dampedGlobalMean_identity {t : ℝ} (ht : 0 < t) (α : ℝ) (N : ℕ) :
    dampedGlobalMean t α N =
      (mixedPrimeSmooth t α N/(N:ℝ))/2 - mixedPrimeSmooth (2*t) α N/(N:ℝ) +
        correctionMean t α N := by
  have hterm (n : ℕ) : primeWeight n * halfDamping t (floorMul α n) *
      globalMinorant t (floorMul α n) =
      (primeWeight n * smoothMangoldt t (floorMul α n))/2 -
        primeWeight n * smoothMangoldt (2*t) (floorMul α n) + correction t α n := by
    rw [mul_assoc, damped_minorant_identity ht]
    unfold correction
    ring
  simp only [dampedGlobalMean, hterm, sum_add_distrib, sum_sub_distrib,
    ← sum_div, mixedPrimeSmooth, correctionMean]
  ring

noncomputable def meanMain (t : ℝ) : ℝ := (dampedMean t - dampedMean (2*t))/(2*t)

lemma meanMain_neg {t : ℝ} (ht : 0 < t) : meanMain t < 0 :=
  div_neg_of_neg_of_pos (sub_neg.mpr (dampedMean_strictMono ht (by linarith)))
    (show 0 < 2*t by positivity)

noncomputable def globalErrorBudget (t α : ℝ) (u : ℕ) : ℝ :=
  primeSmoothErrorBudget t α u / 2 + primeSmoothErrorBudget (2*t) α u +
    correctionMean t α (u^6)

lemma globalErrorBudget_tendsto {t α : ℝ} (ht : 0 < t) (hα : 1 ≤ α) :
    Tendsto (globalErrorBudget t α) atTop (𝓝 0) := by
  have hc := (correctionMean_tendsto ht hα).comp
    (tendsto_pow_atTop (by decide : 6 ≠ 0))
  have hh := (((primeSmoothErrorBudget_tendsto ht α).div_const 2).add
    (primeSmoothErrorBudget_tendsto (show 0 < 2*t by positivity) α)).add hc
  simpa only [globalErrorBudget, zero_div, zero_add] using hh

lemma global_mean_error_budget {t α : ℝ} (ht : 0 < t) (hα : 1 ≤ α) {u : ℕ}
    (hu : 0 < u) (hαu : α ≤ u)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ root64 u →
      |row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6:ℕ)/(d:ℝ)| ≤ primeRowError u) :
    |dampedGlobalMean t α (u^6)-meanMain t| ≤ globalErrorBudget t α u := by
  have h₁ := abs_le.mp (prime_smooth_error_budget hα ht hu hαu hrows)
  have h₂ := abs_le.mp (prime_smooth_error_budget hα (show 0 < 2*t by positivity) hu hαu hrows)
  have hc := correctionMean_nonneg ht α (u^6)
  have he : dampedGlobalMean t α (u^6)-meanMain t =
      (mixedPrimeSmooth t α (u^6)/(u:ℝ)^6-dampedMean t/t)/2 -
        (mixedPrimeSmooth (2*t) α (u^6)/(u:ℝ)^6-dampedMean (2*t)/(2*t)) +
          correctionMean t α (u^6) := by
    rw [dampedGlobalMean_identity ht, meanMain, Nat.cast_pow]
    ring
  rw [he]
  unfold globalErrorBudget
  exact abs_le.mpr ⟨by linarith only [h₁.1, h₂.2, hc],
    by linarith only [h₁.2, h₂.1]⟩

/-- Both smoothing parameters use the SAME row selector, after all
thresholds for their error budgets and the correction term are fixed. -/
theorem exists_global_mean_scale {t α ε : ℝ} (ht : 0 < t)
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧
      |dampedGlobalMean t α (u^6)-meanMain t| < ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_order.mp (globalErrorBudget_tendsto ht hα.le)).2 ε hε).and
      (eventually_ge_atTop ⌈α⌉₊))
  obtain ⟨u, hBu, hu, _, hrows⟩ :=
    exists_small_prime_prefix_rows hα hI (by norm_num : (0:ℝ) < 1) (max B T)
  have hTu : T ≤ u := (le_max_right B T).trans hBu.le
  obtain ⟨he, hαu⟩ := hT u hTu
  have hαu' : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr hαu)
  refine ⟨u, (le_max_left B T).trans_lt hBu, hu, ?_⟩
  exact (global_mean_error_budget ht hα.le hu hαu'
    (fun d hd hdv => hrows d hd hdv (u^6) le_rfl)).trans_lt he

/-- The new global pointwise minorant does not yield a positive mean by
this fixed-parameter, positively damped averaging procedure. -/
theorem exists_negative_global_mean_scale {t α : ℝ} (ht : 0 < t)
    (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ dampedGlobalMean t α (u^6) < meanMain t / 2 ∧
      meanMain t / 2 < 0 := by
  have hm := meanMain_neg ht
  obtain ⟨u, hBu, hu, he⟩ := exists_global_mean_scale ht hα hI
    (show 0 < -meanMain t/2 by linarith) B
  refine ⟨u, hBu, hu, ?_, by linarith⟩
  have hh := (abs_lt.mp he).2
  linarith only [hh]

#print axioms correctionMean_tendsto
#print axioms exists_global_mean_scale
#print axioms exists_negative_global_mean_scale

end Erdos972GlobalMinorantMean
