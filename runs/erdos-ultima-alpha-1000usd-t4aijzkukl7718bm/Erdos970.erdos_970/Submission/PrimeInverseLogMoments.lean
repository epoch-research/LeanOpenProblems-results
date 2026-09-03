import Submission.ReciprocalMertens

/-! Negative logarithmic prime moments, with a uniform additive Mertens
error. These estimates do not assert a lower sieve bound. -/
namespace Erdos970.WeightedMertens
open Finset Real MeasureTheory

noncomputable def logPowerKernel (n : ℕ) (t : ℝ) : ℝ := 1 / (t * log t ^ (n + 2))

lemma hasDerivAt_inv_log_power (n : ℕ) (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => 1 / log x ^ (n + 1))
      (-((n : ℝ) + 1) * logPowerKernel n t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (log_pos ht).ne'
  have hh := ((hasDerivAt_log ht0).pow (n + 1)).inv (pow_ne_zero _ hl)
  simp only [Nat.add_sub_cancel, Pi.pow_apply, Pi.inv_apply] at hh
  change HasDerivAt (fun x : ℝ => (log x ^ (n + 1))⁻¹)
    (-(↑(n + 1) * log t ^ n * t⁻¹) / (log t ^ (n + 1)) ^ 2) t at hh
  convert hh using 1
  · funext x
    simp only [one_div]
  · simp only [Nat.cast_add, Nat.cast_one, logPowerKernel]
    field_simp
    simp only [pow_succ]
    ring

lemma logPowerKernel_continuous (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn (logPowerKernel n) (Set.Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
  have hden : t * log t ^ (n + 2) ≠ 0 := mul_ne_zero ht0 (pow_ne_zero _ hl)
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun x : ℝ => 1 / (x * log x ^ (n + 2))) t
  fun_prop (disch := assumption)

lemma logPowerKernel_integrable (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (logPowerKernel n) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (logPowerKernel_continuous n ha).integrableOn_Icc

lemma logPowerKernel_weighted_integrable (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => realPrimeSum t * logPowerKernel n t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hh := integrableOn_mul_sum_Icc coeff (m := 0) (by linarith : 0 ≤ a)
    (logPowerKernel_continuous n (b := b) ha).integrableOn_Icc
  simpa only [sum_coeff_real, mul_comm] using hh

lemma logPowerKernel_main_integrable (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => log t * logPowerKernel n t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply ContinuousOn.integrableOn_Icc
  exact (continuousOn_log.mono (fun t ht => by
    change t ≠ 0
    linarith [ht.1])).mul (logPowerKernel_continuous n ha)

lemma integral_logPowerKernel (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, logPowerKernel n t) =
      (1 / log a ^ (n + 1) - 1 / log b ^ (n + 1)) / ((n : ℝ) + 1) := by
  have hder : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x => -(1 / log x ^ (n + 1)) / ((n : ℝ) + 1))
        (logPowerKernel n t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    convert ((hasDerivAt_inv_log_power n t (by linarith [ht.1])).neg).div_const ((n : ℝ) + 1) using 1
    field_simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (logPowerKernel_integrable n ha hab)
  rw [hh]
  ring

noncomputable def inverseLogPrimeInterval (n : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, 1 / ((p : ℝ) * log p ^ (n + 1))

lemma inverseLogPrimeInterval_as_sum (n : ℕ) (a b : ℝ) :
    inverseLogPrimeInterval n a b =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (1 / log (p : ℝ) ^ (n + 2)) * coeff p := by
  rw [inverseLogPrimeInterval, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hpp : p.Prime
  · have hl : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hpp.one_lt)).ne'
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    simp only [coeff, hpp, if_true]
    field_simp <;> simp only [pow_succ] <;> ring
  · simp [coeff, hpp]

lemma invLogPower_deriv_integrable (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (deriv (fun t : ℝ => 1 / log t ^ (n + 1))) (Set.Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.congr (continuousOn_const.mul (logPowerKernel_continuous n ha))
  intro t ht
  exact (hasDerivAt_inv_log_power n t (by linarith [ht.1])).deriv

lemma abel_inverseLogPrimeInterval (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    inverseLogPrimeInterval n a b =
      realPrimeSum b / log b ^ (n + 2) - realPrimeSum a / log a ^ (n + 2) +
        ((n : ℝ) + 2) * ∫ t in a..b, realPrimeSum t * logPowerKernel (n + 1) t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      deriv (fun x : ℝ => 1 / log x ^ (n + 2)) t =
        -((n : ℝ) + 2) * logPowerKernel (n + 1) t := by
    convert (hasDerivAt_inv_log_power (n + 1) t (by linarith [ht.1])).deriv using 1 <;> push_cast <;> ring
  rw [inverseLogPrimeInterval_as_sum,
    sum_mul_eq_sub_sub_integral_mul coeff (by linarith : 0 ≤ a) hab
      (fun t ht => (hasDerivAt_inv_log_power (n + 1) t (by linarith [ht.1])).differentiableAt)
      (invLogPower_deriv_integrable (n + 1) ha), ← intervalIntegral.integral_of_le hab]
  simp_rw [sum_coeff_real]
  have he : (∫ t in a..b, deriv (fun x : ℝ => 1 / log x ^ (n + 2)) t * realPrimeSum t) =
      -((n : ℝ) + 2) * ∫ t in a..b, realPrimeSum t * logPowerKernel (n + 1) t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    dsimp only
    rw [hd t ht]
    ring
  rw [he]
  ring

lemma logPowerKernel_main (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, log t * logPowerKernel (n + 1) t) =
      (1 / log a ^ (n + 1) - 1 / log b ^ (n + 1)) / ((n : ℝ) + 1) := by
  rw [← integral_logPowerKernel n ha hab]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
  dsimp only [logPowerKernel]
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
  field_simp

lemma logPowerKernel_error_integrable (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (realPrimeSum t - log t) * logPowerKernel n t) volume a b := by
  simp_rw [sub_mul]
  exact (logPowerKernel_weighted_integrable n ha hab).sub (logPowerKernel_main_integrable n ha hab)

lemma integral_logPowerKernel_error_le (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |∫ t in a..b, (realPrimeSum t - log t) * logPowerKernel n t| ≤
      (boundConstant + 1) *
        ((1 / log a ^ (n + 1) - 1 / log b ^ (n + 1)) / ((n : ℝ) + 1)) := by
  calc
    _ ≤ ∫ t in a..b, |(realPrimeSum t - log t) * logPowerKernel n t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, (boundConstant + 1) * logPowerKernel n t := by
      apply intervalIntegral.integral_mono_on hab (logPowerKernel_error_integrable n ha hab).abs
        ((logPowerKernel_integrable n ha hab).const_mul _)
      intro t ht
      have htk : 0 ≤ logPowerKernel n t := by
        have ht0 : 0 ≤ t := by linarith [ht.1]
        have hl : 0 ≤ log t := log_nonneg (by linarith [ht.1])
        dsimp [logPowerKernel]
        positivity
      rw [abs_mul, abs_of_nonneg htk]
      exact mul_le_mul_of_nonneg_right (abs_realPrimeSum_sub_log t (ha.trans ht.1)) htk
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_logPowerKernel n ha hab]

lemma inverseLogPrimeInterval_error_identity (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    inverseLogPrimeInterval n a b -
        (1 / log a ^ (n + 1) - 1 / log b ^ (n + 1)) / ((n : ℝ) + 1) =
      (realPrimeSum b - log b) / log b ^ (n + 2) -
        (realPrimeSum a - log a) / log a ^ (n + 2) +
        ((n : ℝ) + 2) * ∫ t in a..b, (realPrimeSum t - log t) * logPowerKernel (n + 1) t := by
  have hla : log a ≠ 0 := (log_pos (by linarith)).ne'
  have hlb : log b ≠ 0 := (log_pos (by linarith)).ne'
  have hi : (∫ t in a..b, (realPrimeSum t - log t) * logPowerKernel (n + 1) t) =
      (∫ t in a..b, realPrimeSum t * logPowerKernel (n + 1) t) -
        (1 / log a ^ (n + 1) - 1 / log b ^ (n + 1)) / ((n : ℝ) + 1) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (logPowerKernel_weighted_integrable _ ha hab)
      (logPowerKernel_main_integrable _ ha hab), logPowerKernel_main n ha hab]
  have hqa : log a / log a ^ (n + 2) = 1 / log a ^ (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    field_simp
  have hqb : log b / log b ^ (n + 2) = 1 / log b ^ (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    field_simp
  rw [hi, abel_inverseLogPrimeInterval n ha hab]
  simp only [sub_div, hqa, hqb]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Sharp leading coefficients for every negative logarithmic prime moment,
with an error uniform in the upper endpoint. -/
theorem abs_inverseLogPrimeInterval_sub (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |inverseLogPrimeInterval n a b -
      (1 / log a ^ (n + 1) - 1 / log b ^ (n + 1)) / ((n : ℝ) + 1)| ≤
      2 * (boundConstant + 1) / log a ^ (n + 2) := by
  have hla : 0 < log a := log_pos (by linarith)
  have hlb : 0 < log b := log_pos (by linarith)
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have hb : |(realPrimeSum b - log b) / log b ^ (n + 2)| ≤
      (boundConstant + 1) / log b ^ (n + 2) := by
    rw [abs_div, abs_of_pos (pow_pos hlb _)]
    exact div_le_div_of_nonneg_right (abs_realPrimeSum_sub_log b (ha.trans hab)) (pow_pos hlb _).le
  have hA : |(realPrimeSum a - log a) / log a ^ (n + 2)| ≤
      (boundConstant + 1) / log a ^ (n + 2) := by
    rw [abs_div, abs_of_pos (pow_pos hla _)]
    exact div_le_div_of_nonneg_right (abs_realPrimeSum_sub_log a ha) (pow_pos hla _).le
  have herror := integral_logPowerKernel_error_le (n + 1) ha hab
  norm_num only [Nat.cast_add, Nat.cast_one] at herror
  rw [inverseLogPrimeInterval_error_identity n ha hab]
  calc
    _ ≤ |(realPrimeSum b - log b) / log b ^ (n + 2) -
          (realPrimeSum a - log a) / log a ^ (n + 2)| +
        |((n : ℝ) + 2) * ∫ t in a..b, (realPrimeSum t - log t) * logPowerKernel (n + 1) t| :=
      abs_add_le _ _
    _ ≤ |(realPrimeSum b - log b) / log b ^ (n + 2)| +
        |(realPrimeSum a - log a) / log a ^ (n + 2)| +
        ((n : ℝ) + 2) * |∫ t in a..b, (realPrimeSum t - log t) * logPowerKernel (n + 1) t| := by
      rw [abs_mul, abs_of_pos hn]
      exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ (boundConstant + 1) / log b ^ (n + 2) + (boundConstant + 1) / log a ^ (n + 2) +
        ((n : ℝ) + 2) * ((boundConstant + 1) *
          ((1 / log a ^ (n + 2) - 1 / log b ^ (n + 2)) / ((n : ℝ) + 2))) := by
      gcongr
      convert herror using 1 <;> ring
    _ = _ := by field_simp; ring

#print axioms integral_logPowerKernel
#print axioms abel_inverseLogPrimeInterval
#print axioms abs_inverseLogPrimeInterval_sub
end Erdos970.WeightedMertens
