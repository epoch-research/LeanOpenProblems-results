import Submission.DampedMeanZeta

/-! An explicit scalar truncation estimate, uniform in positive damping.
This is an absolute bound, not cancellation of divisor rows. -/
namespace Erdos972DampedMeanTailBound

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972FixedDampedCorrelation Erdos972SmoothDivisorTail
open Erdos972DivisorCovariance Erdos972DampedDivisorKernel

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma reciprocalWeight_eq_rpow {t : ℝ} {n : ℕ} (hn : 0 < n) :
    reciprocalWeight t n = (n : ℝ)^(-t-1) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.rpow_sub hnR, Real.rpow_one, Real.rpow_def_of_pos hnR]
  unfold reciprocalWeight
  congr 2
  ring

lemma reciprocalWeight_interval_bound {t : ℝ} (ht : 0 < t) {D M : ℕ}
    (hD : 0 < D) (hDM : D ≤ M) :
    (∑ n ∈ Ioc D M, reciprocalWeight t n) ≤ damping t D / t := by
  have hDR : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr (hD.trans_le hDM)
  have hant : AntitoneOn (fun x : ℝ => x^(-t-1)) (Set.Icc D M) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hDR.trans_le hx.1) hxy (by linarith)
  have hh := hant.sum_le_integral_Ico hDM
  have heq : (∑ n ∈ Ioc D M, reciprocalWeight t n) =
      ∑ n ∈ Ico D M, ((n+1 : ℕ) : ℝ)^(-t-1) := by
    rw [sum_Ico_add' (fun n : ℕ => (n : ℝ)^(-t-1)) D M 1, Ico_add_one_add_one_eq_Ioc]
    apply sum_congr rfl
    intro n hn
    exact reciprocalWeight_eq_rpow (hD.trans (mem_Ioc.mp hn).1)
  rw [heq]
  apply hh.trans
  have hnot : (0:ℝ) ∉ Set.uIcc (D:ℝ) (M:ℝ) := by
    rw [Set.uIcc_of_le (Nat.cast_le.mpr hDM)]
    exact fun h => (not_le.mpr hDR) h.1
  rw [integral_rpow (Or.inr ⟨by linarith, hnot⟩)]
  have hpow : -t-1+1 = -t := by ring
  rw [hpow]
  have heD : (D:ℝ)^(-t) = damping t D := by
    rw [Real.rpow_def_of_pos hDR]
    unfold damping
    congr 1
    ring
  rw [heD]
  have hp : 0 ≤ (M:ℝ)^(-t) := Real.rpow_nonneg hMR.le _
  have he : ((M:ℝ)^(-t)-damping t D)/(-t) =
      (damping t D-(M:ℝ)^(-t))/t := by ring
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith only [hp]) ht.le

lemma dampedMean_interval_error {t : ℝ} (ht : 0 < t) {D M : ℕ}
    (hD : 0 < D) (hDM : D ≤ M) :
    |divisorMean M (dampedCoefficient t)-divisorMean D (dampedCoefficient t)| ≤
      damping t D/t := by
  have he : divisorMean M (dampedCoefficient t)-divisorMean D (dampedCoefficient t) =
      ∑ n ∈ Ioc D M, dampedCoefficient t n / n := by
    unfold divisorMean
    rw [← sum_Ioc_consecutive (fun n : ℕ => dampedCoefficient t n / n) (show 0 ≤ D by omega) hDM]
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (fun n hn => ?_)).trans (reciprocalWeight_interval_bound ht hD hDM)
  have hmu : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
  simp only [dampedCoefficient, abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  unfold reciprocalWeight
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (Real.exp_pos _).le

/-- All parameters in this tail bound are explicit. -/
theorem dampedMean_tail_bound {t : ℝ} (ht : 0 < t) {D : ℕ} (hD : 0 < D) :
    |divisorMean D (dampedCoefficient t)-dampedMean t| ≤ damping t D/t := by
  have hh := ((divisorMean_tendsto ht).sub_const (divisorMean D (dampedCoefficient t))).abs
  have hb := le_of_tendsto hh (by
    filter_upwards [eventually_ge_atTop D] with M hM
    exact dampedMean_interval_error ht hD hM)
  rwa [abs_sub_comm] at hb

#print axioms dampedMean_tail_bound

end Erdos972DampedMeanTailBound
