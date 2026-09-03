import Submission.FixedDampedCorrelation

/-! Evaluation and the small-parameter asymptotic of the scalar damped mean.
This evaluates an iterated limit; it does not exchange it with the mean at
infinity. -/
namespace Erdos972DampedMeanZeta

open Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972FixedDampedCorrelation Erdos972SmoothDivisorTail Erdos972MobiusLaplace

lemma complex_damped_term (t : ℝ) (n : ℕ) :
    ((dampedCoefficient t n / n : ℝ) : ℂ) =
      LSeries.term (fun n => (μ n : ℂ)) (1+(t : ℂ)) n := by
  by_cases hn : n = 0
  · simp [hn]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hr : dampedCoefficient t n/n = (μ n : ℝ)/(n : ℝ)^(1+t) := by
    rw [Real.rpow_add hnR, Real.rpow_one, Real.rpow_def_of_pos hnR]
    unfold dampedCoefficient
    rw [show -t*Real.log n = -(Real.log n*t) by ring, Real.exp_neg]
    ring
  rw [LSeries.term_of_ne_zero hn]
  simpa only [Complex.ofReal_div, Complex.ofReal_intCast,
    Complex.ofReal_cpow hnR.le, Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_one]
    using congrArg (fun x : ℝ => (x : ℂ)) hr

lemma dampedMean_eq_LSeries (t : ℝ) :
    (dampedMean t : ℂ) = LSeries (fun n => (μ n : ℂ)) (1+(t : ℂ)) := by
  rw [dampedMean, Complex.ofReal_tsum]
  exact tsum_congr (complex_damped_term t)

lemma zeta_mul_dampedMean {t : ℝ} (ht : 0 < t) :
    riemannZeta (1+(t : ℂ)) * (dampedMean t : ℂ) = 1 := by
  have hst : 1 < (1+(t : ℂ)).re := by simpa using ht
  rw [dampedMean_eq_LSeries, ← LSeries_zeta_eq_riemannZeta hst]
  exact LSeries_zeta_mul_Lseries_moebius hst

lemma dampedMean_div_eq_regularZeta {t : ℝ} (ht : 0 < t) :
    ((dampedMean t/t : ℝ) : ℂ) = (regularZeta (1+(t : ℂ)))⁻¹ := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have ht1 : 1+(t : ℂ) ≠ 1 := by simpa using htC
  have hreg : regularZeta (1+(t : ℂ)) = (t : ℂ)*riemannZeta (1+(t : ℂ)) := by
    rw [regularZeta, Function.update_of_ne ht1]
    congr 1
    ring
  have hz : regularZeta (1+(t : ℂ)) ≠ 0 :=
    regularZeta_ne_zero (by simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith)
  rw [inv_eq_one_div]
  apply (eq_div_iff hz).mpr
  rw [hreg, Complex.ofReal_div]
  have he : (dampedMean t : ℂ)/(t : ℂ)*((t : ℂ)*riemannZeta (1+(t : ℂ))) =
      riemannZeta (1+(t : ℂ))*(dampedMean t : ℂ) := by field_simp
  rw [he, zeta_mul_dampedMean ht]

/-- The scalar factor in the iterated normalized smoothing limit tends to
one. There is still no uniform-in-t outer mean theorem here. -/
theorem dampedMean_div_tendsto_one :
    Tendsto (fun t : ℝ => dampedMean t/t) (𝓝[>] 0) (𝓝 1) := by
  have hs : Tendsto (fun t : ℝ => 1+(t : ℂ)) (𝓝 0) (𝓝 (1 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).const_add (1 : ℂ)
  have hz := continuous_regularZeta.continuousAt.tendsto.comp hs
  rw [regularZeta_one] at hz
  have hi := (hz.inv₀ (by norm_num : (1 : ℂ) ≠ 0)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hi
  simp only [inv_one, Complex.one_re] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hh := congrArg Complex.re (dampedMean_div_eq_regularZeta ht)
  simpa only [Complex.ofReal_re] using hh.symm

#print axioms dampedMean_eq_LSeries
#print axioms dampedMean_div_tendsto_one

end Erdos972DampedMeanZeta
