import Submission.WeightedMertens

/-! Partial summation of the weighted Mertens estimate. -/
namespace Erdos970.WeightedMertens
open Finset Real MeasureTheory

noncomputable def realPrimeSum (x : ℝ) : ℝ := primeSum ⌊x⌋₊

lemma abs_realPrimeSum_sub_log (x : ℝ) (hx : 2 ≤ x) :
    |realPrimeSum x - log x| ≤ boundConstant + 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hn2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hn : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  have hfloor := Nat.floor_le hx0
  have hlt := Nat.lt_floor_add_one x
  have hlog := log_le_log hn hfloor
  have hdiff : log x - log ⌊x⌋₊ ≤ 1 := by
    rw [← log_div (by linarith : x ≠ 0) hn.ne']
    have hd := log_le_sub_one_of_pos (div_pos (by linarith : 0 < x) hn)
    have hratio : x / (⌊x⌋₊ : ℝ) ≤ 2 := by
      apply (div_le_iff₀ hn).mpr
      have hone : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊x⌋₊)
      linarith
    linarith
  have h := abs_le.mp (abs_primeSum_sub_log ⌊x⌋₊ (by omega))
  rw [abs_le]
  dsimp only [realPrimeSum]
  constructor <;> linarith

noncomputable def coeff (n : ℕ) : ℝ := if n.Prime then log n / n else 0

lemma sum_coeff (n : ℕ) : ∑ k ∈ Icc 0 n, coeff k = primeSum n := by
  simp only [coeff, ← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, mem_Icc, mem_primes, Nat.zero_le, true_and, and_comm]

lemma sum_coeff_real (x : ℝ) :
    ∑ k ∈ Icc 0 ⌊x⌋₊, coeff k = realPrimeSum x := sum_coeff _

noncomputable def reciprocalInterval (a b : ℝ) : ℝ :=
  ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, (p : ℝ)⁻¹

lemma reciprocal_as_sum (a b : ℝ) :
    reciprocalInterval a b = ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (log (p : ℝ))⁻¹ * coeff p := by
  rw [reciprocalInterval, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hpp : p.Prime
  · have hl : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hpp.one_lt)).ne'
    simp only [hpp, if_true, coeff]
    field_simp
  · simp [coeff, hpp]

lemma invLog_differentiable {a b : ℝ} (ha : 2 ≤ a) :
    ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun x => (log x)⁻¹) t := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
  fun_prop (disch := assumption)

lemma invLog_deriv_integrable {a b : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (deriv (fun x : ℝ => (log x)⁻¹)) (Set.Icc a b) := by
  refine ContinuousOn.integrableOn_Icc fun t ht => ContinuousWithinAt.congr ?_
    (fun _ _ => deriv_inv_log) deriv_inv_log
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ^ 2 ≠ 0 := pow_ne_zero 2 (log_pos (by linarith [ht.1])).ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

lemma abel_reciprocal {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    reciprocalInterval a b = realPrimeSum b / log b - realPrimeSum a / log a +
      ∫ t in a..b, realPrimeSum t / (t * log t ^ 2) := by
  rw [reciprocal_as_sum,
    sum_mul_eq_sub_sub_integral_mul coeff (by linarith : 0 ≤ a) hab
      (invLog_differentiable ha) (invLog_deriv_integrable ha),
    ← intervalIntegral.integral_of_le hab]
  simp_rw [sum_coeff_real, deriv_inv_log]
  have heq : (fun t => -t⁻¹ / log t ^ 2 * realPrimeSum t) =
      (fun t => -(realPrimeSum t / (t * log t ^ 2))) := by
    funext t
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, intervalIntegral.integral_neg]
  ring

noncomputable def kernel (t : ℝ) : ℝ := 1 / (t * log t ^ 2)

lemma kernel_continuous {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn kernel (Set.Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
  have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
  exact ContinuousAt.continuousWithinAt (by change ContinuousAt (fun x : ℝ => 1 / (x * log x ^ 2)) t; fun_prop (disch := assumption))

lemma kernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable kernel volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (kernel_continuous ha).integrableOn_Icc

lemma weighted_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => realPrimeSum t * kernel t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have h := integrableOn_mul_sum_Icc coeff (m := 0) (by linarith : 0 ≤ a)
    (kernel_continuous (b := b) ha).integrableOn_Icc
  simpa only [sum_coeff_real, mul_comm] using h

lemma main_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => log t * kernel t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine ContinuousOn.integrableOn_Icc ?_
  apply ContinuousOn.mul _ (kernel_continuous ha)
  exact continuousOn_log.mono (fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1])

lemma integral_kernel {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, kernel t = (log a)⁻¹ - (log b)⁻¹ := by
  have hder : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => -(log t)⁻¹) (kernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    convert ((hasDerivAt_log ht0).inv hl).neg using 1
    dsimp [kernel]
    field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (kernel_integrable ha hab)
  linarith

lemma integral_main {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t * kernel t = log (log b) - log (log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (main_integrable ha hab)
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
  convert (hasDerivAt_log ht0).log hl using 1
  dsimp [kernel]
  field_simp

lemma error_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (realPrimeSum t - log t) * kernel t) volume a b := by
  simp_rw [sub_mul]
  exact (weighted_integrable ha hab).sub (main_integrable ha hab)

lemma integral_error_le {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |∫ t in a..b, (realPrimeSum t - log t) * kernel t| ≤
      (boundConstant + 1) * ((log a)⁻¹ - (log b)⁻¹) := by
  calc
    _ ≤ ∫ t in a..b, |(realPrimeSum t - log t) * kernel t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, (boundConstant + 1) * kernel t := by
      apply intervalIntegral.integral_mono_on hab (error_integrable ha hab).abs
        ((kernel_integrable ha hab).const_mul _)
      intro t ht
      have htk : 0 ≤ kernel t := by
        have : 0 ≤ t := by linarith [ht.1]
        dsimp [kernel]
        positivity
      rw [abs_mul, abs_of_nonneg htk]
      exact mul_le_mul_of_nonneg_right (abs_realPrimeSum_sub_log t (ha.trans ht.1)) htk
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_kernel ha hab]

lemma reciprocal_error_identity {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    reciprocalInterval a b - (log (log b) - log (log a)) =
      (realPrimeSum b - log b) / log b - (realPrimeSum a - log a) / log a +
        ∫ t in a..b, (realPrimeSum t - log t) * kernel t := by
  have hla : log a ≠ 0 := (log_pos (by linarith)).ne'
  have hlb : log b ≠ 0 := (log_pos (by linarith)).ne'
  have hi : (∫ t in a..b, (realPrimeSum t - log t) * kernel t) =
      (∫ t in a..b, realPrimeSum t / (t * log t ^ 2)) -
        (log (log b) - log (log a)) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (weighted_integrable ha hab) (main_integrable ha hab),
      integral_main ha hab]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp [kernel, div_eq_mul_inv]
  rw [hi, abel_reciprocal ha hab]
  field_simp
  <;> ring

/-- A sharp-coefficient reciprocal-prime increment estimate, uniform in the upper endpoint. -/
theorem abs_reciprocalInterval_sub_loglog {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |reciprocalInterval a b - (log (log b) - log (log a))| ≤
      2 * (boundConstant + 1) / log a := by
  have hla : 0 < log a := log_pos (by linarith)
  have hlb : 0 < log b := log_pos (by linarith)
  have hb : |(realPrimeSum b - log b) / log b| ≤ (boundConstant + 1) / log b := by
    rw [abs_div, abs_of_pos hlb]
    exact div_le_div_of_nonneg_right (abs_realPrimeSum_sub_log b (ha.trans hab)) hlb.le
  have hA : |(realPrimeSum a - log a) / log a| ≤ (boundConstant + 1) / log a := by
    rw [abs_div, abs_of_pos hla]
    exact div_le_div_of_nonneg_right (abs_realPrimeSum_sub_log a ha) hla.le
  rw [reciprocal_error_identity ha hab]
  calc
    _ ≤ |(realPrimeSum b - log b) / log b - (realPrimeSum a - log a) / log a| +
        |∫ t in a..b, (realPrimeSum t - log t) * kernel t| := abs_add_le _ _
    _ ≤ |(realPrimeSum b - log b) / log b| + |(realPrimeSum a - log a) / log a| +
        |∫ t in a..b, (realPrimeSum t - log t) * kernel t| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ (boundConstant + 1) / log b + (boundConstant + 1) / log a +
        (boundConstant + 1) * ((log a)⁻¹ - (log b)⁻¹) := by
      gcongr
      exact integral_error_le ha hab
    _ = _ := by ring

#print axioms abs_reciprocalInterval_sub_loglog
end Erdos970.WeightedMertens
