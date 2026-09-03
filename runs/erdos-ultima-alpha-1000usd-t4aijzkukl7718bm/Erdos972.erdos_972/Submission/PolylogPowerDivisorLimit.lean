import Submission.PolylogPowerPrimeDetector
import Submission.GcdProfileExpansion
import Submission.SmoothDivisorTail

/-! Fixed-divisor limits of the adaptive polylogarithmic-power detector.
The coefficients tend to the ordinary Möbius coefficients. This is not
an estimate for the full divisor tail or a prime-pair lower bound. -/
namespace Erdos972PolylogPowerDivisorLimit

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972PolylogMomentPrimeProxy Erdos972PolylogPowerPrimeDetector
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972GcdProfileExpansion Erdos972NonlinearPrimeProxy

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma logSize_tendsto_nat : Tendsto logSize atTop atTop := by
  apply tendsto_atTop.2
  intro B
  exact eventually_atTop.2 ⟨2^B, fun n hn =>
    (Nat.le_log_of_pow_le (by decide : 1 < 2) hn).trans (Nat.le_succ _)⟩

lemma logSize_tendsto : Tendsto (fun n : ℕ => (logSize n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp logSize_tendsto_nat

lemma parameter_upper {n : ℕ} (hn : 1 < n) :
    parameter n ≤ (16 / Real.log 2) * (Real.log (logSize n) / logSize n) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (0 : ℝ) < logSize n := Nat.cast_pos.mpr (logSize_pos n)
  have hL2 : (2 : ℝ) ≤ logSize n := by exact_mod_cast two_le_logSize hn
  have hk : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have hh := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      (show (2 : ℝ)^(Nat.log 2 n) ≤ n by exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0))
    simpa only [Real.log_pow] using hh
  have he : (logSize n : ℝ) = (Nat.log 2 n : ℝ) + 1 := by simp [logSize]
  have hlo : (logSize n : ℝ)*Real.log 2/2 ≤ Real.log n := by
    nlinarith only [hk, he, hL2, h2]
  have hbase : (0 : ℝ) < (logSize n : ℝ)*Real.log 2/2 := by positivity
  unfold parameter
  calc
    _ ≤ 8 * Real.log (logSize n) / ((logSize n : ℝ)*Real.log 2/2) :=
      div_le_div_of_nonneg_left (by positivity) hbase hlo
    _ = _ := by field_simp; ring

lemma parameter_tendsto_zero : Tendsto parameter atTop (𝓝 0) := by
  have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    logSize_tendsto).const_mul (16 / Real.log 2)
  simp only [Function.comp_def, id_eq, mul_zero] at hh
  exact squeeze_zero' (Eventually.of_forall parameter_nonneg)
    ((eventually_gt_atTop 1).mono fun n hn => parameter_upper hn) hh

noncomputable def adaptiveProfile (n d : ℕ) : ℝ :=
  (expDivisorSum (parameter n) d)^(powerBudget n)

noncomputable def adaptiveCoeff (n d : ℕ) : ℝ :=
  profileCoeff (adaptiveProfile n) d

lemma adaptiveProfile_one (n : ℕ) : adaptiveProfile n 1 = 1 := by
  simp [adaptiveProfile, expDivisorSum]

lemma adaptiveProfile_tendsto_zero {d : ℕ} (hd : d ≠ 1) :
    Tendsto (fun n => adaptiveProfile n d) atTop (𝓝 0) := by
  have he := (hasDerivAt_expDivisorSum d).continuousAt.tendsto.comp parameter_tendsto_zero
  simp only [expDivisorSum_at_zero, one_apply, if_neg hd] at he
  apply squeeze_zero (fun n => pow_nonneg (expDivisorSum_nonneg (parameter_nonneg n) d) _)
    (fun n => ?_) he
  have hbudget : 1 ≤ powerBudget n := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (logSize_pos n).ne')
  simpa only [pow_one] using pow_le_pow_of_le_one
    (expDivisorSum_nonneg (parameter_nonneg n) d)
    (Erdos972SmoothDivisorTail.expDivisorSum_le_one (parameter_nonneg n) d) hbudget

lemma adaptiveProfile_tendsto (d : ℕ) :
    Tendsto (fun n => adaptiveProfile n d) atTop (𝓝 (if d = 1 then 1 else 0)) := by
  by_cases hd : d = 1
  · subst d
    simpa only [adaptiveProfile_one, if_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · simpa only [if_neg hd] using adaptiveProfile_tendsto_zero hd

/-- Each fixed divisor coefficient tends to the corresponding Möbius value;
the moving power does not make these coefficients small. -/
theorem adaptiveCoeff_tendsto (d : ℕ) :
    Tendsto (fun n => adaptiveCoeff n d) atTop (𝓝 (μ d : ℝ)) := by
  have hh := tendsto_finset_sum d.divisors (fun e _ =>
    (adaptiveProfile_tendsto e).mul_const (μ (d/e) : ℝ))
  have hs : (∑ e ∈ d.divisors, (if e = 1 then (1 : ℝ) else 0) * (μ (d/e) : ℝ)) =
      (μ d : ℝ) := by
    by_cases hd : d = 0
    · subst d
      simp
    · rw [sum_eq_single 1]
      · simp
      · intro e he hne
        simp [hne]
      · intro hnot
        exact (hnot (Nat.mem_divisors.mpr ⟨one_dvd d, hd⟩)).elim
  simpa only [adaptiveCoeff, profileCoeff_eq_sum, hs] using hh

noncomputable def truncatedDetector (D n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 D, if d ∣ n then adaptiveCoeff n d else 0

noncomputable def truncatedMobius (D n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 D, if d ∣ n then (μ d : ℝ) else 0

lemma full_divisor_identity {n : ℕ} (hn : 1 < n) :
    powerDetector n = ∑ d ∈ n.divisors, adaptiveCoeff n d := by
  simp only [adaptiveCoeff]
  rw [sum_profileCoeff (adaptiveProfile n) (by omega : n ≠ 0)]
  simp only [powerDetector, if_pos hn, adaptiveProfile]

lemma truncatedDetector_eq_divisor_sum {n : ℕ} (hn : 0 < n) (D : ℕ) :
    truncatedDetector D n = ∑ d ∈ n.divisors.filter (fun d => d ≤ D), adaptiveCoeff n d := by
  unfold truncatedDetector
  rw [← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd0, hdD⟩, hdn⟩
    exact ⟨⟨hdn, hn.ne'⟩, hdD⟩
  · rintro ⟨⟨hdn, _⟩, hdD⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn, hdD⟩, hdn⟩

lemma truncation_difference_bound (D n : ℕ) :
    |truncatedDetector D n - truncatedMobius D n| ≤
      ∑ d ∈ Ioc 0 D, |adaptiveCoeff n d - (μ d : ℝ)| := by
  unfold truncatedDetector truncatedMobius
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn, le_refl]
  · simpa only [if_neg hdn, sub_self, abs_zero] using abs_nonneg (adaptiveCoeff n d - (μ d : ℝ))

/-- For every fixed cutoff, the actual moving-coefficient truncation is
asymptotic to the usual periodic truncated Möbius divisor sum. -/
theorem truncatedDetector_sub_mobius_tendsto (D : ℕ) :
    Tendsto (fun n => truncatedDetector D n - truncatedMobius D n) atTop (𝓝 0) := by
  have hh := tendsto_finset_sum (Ioc 0 D) (fun d _ =>
    ((adaptiveCoeff_tendsto d).sub_const (μ d : ℝ)).abs)
  simp only [sub_self, abs_zero, sum_const_zero] at hh
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero (fun n => abs_nonneg _) (truncation_difference_bound D) hh)

#print axioms parameter_tendsto_zero
#print axioms adaptiveCoeff_tendsto
#print axioms truncatedDetector_sub_mobius_tendsto

end Erdos972PolylogPowerDivisorLimit
