import Submission.MobiusPartialSums

/-! The Laplace transform of reciprocal Möbius sums and its continuous
boundary on the closed right half-plane. -/
namespace Erdos972MobiusLaplace

open Finset Filter MeasureTheory Set ArithmeticFunction Asymptotics Classical
open scoped ArithmeticFunction.Moebius Topology
open Erdos972MobiusPartialSums Erdos972ChebyshevPNT

noncomputable def regularZeta : ℂ → ℂ :=
  Function.update (fun s => (s-1)*riemannZeta s) 1 1

lemma regularZeta_one : regularZeta 1 = 1 := by simp [regularZeta]

lemma continuous_regularZeta : Continuous regularZeta := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s = 1
  · subst s
    exact continuousAt_update_same.mpr riemannZeta_residue_one
  · unfold regularZeta
    rw [continuousAt_update_of_ne hs]
    exact (continuousAt_id.sub continuousAt_const).mul (differentiableAt_riemannZeta hs).continuousAt

lemma regularZeta_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : regularZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · rw [hs1, regularZeta_one]
    exact one_ne_zero
  · rw [regularZeta, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs)

noncomputable def boundary (v : ℝ × ℝ) : ℂ :=
  1/regularZeta (1+((v.1 : ℂ)+(2*Real.pi*v.2 : ℝ)*Complex.I))

lemma continuousOn_boundary : ContinuousOn boundary {v | 0 ≤ v.1 ∧ v.1 ≤ 1} := by
  let s : ℝ × ℝ → ℂ := fun v => 1+((v.1 : ℂ)+(2*Real.pi*v.2 : ℝ)*Complex.I)
  have hc : Continuous s := by dsimp [s]; fun_prop
  apply continuousOn_const.div (continuous_regularZeta.comp hc).continuousOn
  intro v hv
  apply regularZeta_ne_zero
  simp only [s, Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  linarith only [hv.1]

noncomputable def weightedMoebius (n : ℕ) : ℂ := (μ n : ℂ)/(n : ℂ)

lemma weightedMoebius_partial (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, weightedMoebius n) = (reciprocalMoebius N : ℂ) := by
  simp only [weightedMoebius, reciprocalMoebius, Complex.ofReal_sum, Complex.ofReal_div,
    Complex.ofReal_intCast, Complex.ofReal_natCast]
  congr 1

lemma term_weightedMoebius (z : ℂ) (n : ℕ) :
    LSeries.term weightedMoebius z n = LSeries.term (fun n => (μ n : ℂ)) (1+z) n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [LSeries.term_of_ne_zero hn, weightedMoebius, Complex.cpow_add 1 z hnC, Complex.cpow_one, div_div]

lemma LSeries_weightedMoebius (z : ℂ) :
    LSeries weightedMoebius z = LSeries (fun n => (μ n : ℂ)) (1+z) := by
  unfold LSeries
  exact tsum_congr (term_weightedMoebius z)

lemma LSeriesSummable_weightedMoebius {z : ℂ} (hz : 0 < z.re) :
    LSeriesSummable weightedMoebius z := by
  simp only [LSeriesSummable, funext (term_weightedMoebius z)]
  exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by simpa using hz)

lemma weightedMoebius_partial_bigO :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, weightedMoebius n) =O[atTop]
      (fun N => (N : ℝ)^(0 : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards with N
  simp only [weightedMoebius_partial, Complex.norm_real, Real.norm_eq_abs, Real.rpow_zero, abs_one, mul_one]
  exact reciprocalMoebius_bound N

lemma weightedMoebius_integral {z : ℂ} (hz : 0 < z.re) :
    LSeries (fun n => (μ n : ℂ)) (1+z) =
      z*∫ x in Ioi (1 : ℝ), (reciprocalMoebiusReal x : ℂ)*(x : ℂ)^(-(z+1)) := by
  have hh := LSeries_eq_mul_integral weightedMoebius (by norm_num : (0 : ℝ) ≤ 0) hz
    (LSeriesSummable_weightedMoebius hz) weightedMoebius_partial_bigO
  rw [LSeries_weightedMoebius] at hh
  simpa only [weightedMoebius_partial, reciprocalMoebiusReal] using hh

lemma logMoebius_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-z*t)*(logMoebius t : ℂ)) =
      LSeries (fun n => (μ n : ℂ)) (1+z)/z := by
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  have hh := weightedMoebius_integral hz
  have hi : (∫ x in Ioi (1 : ℝ), (reciprocalMoebiusReal x : ℂ)*(x : ℂ)^(-(z+1))) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-z*t)*(logMoebius t : ℂ) := by
    rw [← exp_image_Ioi_zero,
      integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (Real.exp_monotone.monotoneOn _)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp only
    rw [exp_cpow]
    simp only [logMoebius, if_pos ht, Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
    have he : Complex.exp (t : ℂ)*Complex.exp ((t : ℂ)*(-(z+1))) = Complex.exp (-z*t) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      Complex.exp (t : ℂ)*((reciprocalMoebiusReal (Real.exp t) : ℂ)*Complex.exp ((t : ℂ)*(-(z+1)))) =
          (Complex.exp (t : ℂ)*Complex.exp ((t : ℂ)*(-(z+1))))*(reciprocalMoebiusReal (Real.exp t) : ℂ) := by ring
      _ = _ := by rw [he]
  rw [hi] at hh
  rw [hh]
  field_simp

lemma logMoebius_laplace_boundary (ε ξ : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-((ε : ℂ)+(2*Real.pi*ξ : ℝ)*Complex.I)*t)*(logMoebius t : ℂ)) =
      boundary (ε, ξ) := by
  let z : ℂ := (ε : ℂ)+(2*Real.pi*ξ : ℝ)*Complex.I
  have hzre : z.re = ε := by simp [z]
  have hz : 0 < z.re := hzre ▸ hε
  have hs : 1 < (1+z).re := by simpa using hz
  have hsne : 1+z ≠ 1 := by
    intro hh
    have he := congrArg Complex.re hh
    simp only [Complex.add_re, Complex.one_re, hzre] at he
    linarith only [he, hε]
  have hζ := riemannZeta_ne_zero_of_one_le_re hs.le
  have hμ := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hμ
  have hμ' : LSeries (fun n => (μ n : ℂ)) (1+z) = 1/riemannZeta (1+z) := by
    apply (eq_div_iff hζ).mpr
    simpa only [mul_comm] using hμ
  change (∫ t in Ioi (0 : ℝ), Complex.exp (-z*t)*(logMoebius t : ℂ)) = 1/regularZeta (1+z)
  rw [logMoebius_laplace hz, hμ', regularZeta, Function.update_of_ne hsne]
  have he : 1+z-1 = z := by ring
  rw [he, div_div, mul_comm (riemannZeta (1+z)) z]

/-- The signed reciprocal Möbius sum tends to zero. This uses the continuous
zero-free zeta boundary and the proved signed slow-oscillation Tauberian theorem. -/
theorem logMoebius_tendsto_zero : Tendsto logMoebius atTop (𝓝 0) := by
  apply Erdos972SlowOscillationTauberian.bounded_slow_laplace_tauberian
    measurable_logMoebius (fun t ht => by simp only [logMoebius, if_neg (not_lt.mpr ht)])
    2 logMoebius_bound logMoebius_slow boundary continuousOn_boundary logMoebius_laplace_boundary

/-- The form used in the common logarithmic main coefficients. -/
theorem reciprocalMoebius_tendsto_zero : Tendsto reciprocalMoebius atTop (𝓝 0) := by
  have hh := logMoebius_tendsto_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  simp only [Function.comp_apply, logMoebius, if_pos (Real.log_pos hN1),
    Real.exp_log (by linarith : (0 : ℝ)<N), reciprocalMoebiusReal, Nat.floor_natCast]

#print axioms reciprocalMoebius_tendsto_zero

end Erdos972MobiusLaplace
