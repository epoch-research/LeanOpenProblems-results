import Submission.BoundedTauberian
import Submission.PrimeDirichletPole

/-! The prime number theorem for Chebyshev's functions, obtained from the
continuous boundary remainder and a proved bounded Laplace-Tauberian theorem. -/
namespace Erdos972ChebyshevPNT

open MeasureTheory Set Filter Finset ArithmeticFunction Asymptotics
open scoped Topology
open Erdos972PrimeDirichletPole Erdos972BoundedTauberian

lemma psi_monotone : Monotone Chebyshev.psi := by
  intro x y hxy
  unfold Chebyshev.psi
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans (Nat.floor_mono hxy)⟩
  · intro n _ _
    exact vonMangoldt_nonneg

lemma measurable_psi : Measurable Chebyshev.psi := psi_monotone.measurable

noncomputable def normalizedPsi (t : ℝ) : ℝ :=
  Real.exp (-t) * Chebyshev.psi (Real.exp t)

lemma normalizedPsi_nonneg (t : ℝ) : 0 ≤ normalizedPsi t :=
  mul_nonneg (Real.exp_pos _).le (Chebyshev.psi_nonneg _)

lemma normalizedPsi_zero {t : ℝ} (ht : t ≤ 0) : normalizedPsi t = 0 := by
  have he : Real.exp t < 2 := (Real.exp_le_one_iff.mpr ht).trans_lt (by norm_num)
  simp [normalizedPsi, Chebyshev.psi_eq_zero_of_lt_two he]

lemma normalizedPsi_le (t : ℝ) : normalizedPsi t ≤ Real.log 4 + 4 := by
  have h := mul_le_mul_of_nonneg_left
    (Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le) (Real.exp_pos (-t)).le
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ Real.exp (-t) * ((Real.log 4 + 4) * Real.exp t) := h
    _ = (Real.log 4 + 4) * (Real.exp (-t) * Real.exp t) := by ring
    _ = Real.log 4 + 4 := by rw [he, mul_one]

lemma measurable_normalizedPsi : Measurable normalizedPsi :=
  (Real.continuous_exp.comp continuous_neg).measurable.mul
    (measurable_psi.comp Real.continuous_exp.measurable)

lemma exp_mul_normalizedPsi (t : ℝ) :
    Real.exp t * normalizedPsi t = Chebyshev.psi (Real.exp t) := by
  rw [normalizedPsi, ← mul_assoc, ← Real.exp_add]
  simp

lemma monotone_exp_mul_normalizedPsi :
    Monotone (fun t => Real.exp t * normalizedPsi t) := by
  simp_rw [exp_mul_normalizedPsi]
  exact psi_monotone.comp Real.exp_monotone

lemma psi_sum_Icc (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, Λ k) = Chebyshev.psi n := by
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  congr 1

lemma psi_partial_bigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, Λ k) =O[atTop] (fun n => (n : ℝ) ^ (1 : ℝ)) := by
  apply IsBigO.of_bound (Real.log 4 + 4)
  filter_upwards with n
  simp only [psi_sum_Icc, Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg _), abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

lemma mangoldt_integral_representation {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) s =
      s * ∫ x in Ioi (1 : ℝ), (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg vonMangoldt zero_le_one hs
    psi_partial_bigO (fun _ => vonMangoldt_nonneg)
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  congr 1
  rw [← Complex.ofReal_sum, psi_sum_Icc]
  simp [Chebyshev.psi]

lemma exp_image_Ioi_zero : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact Real.one_lt_exp_iff.mpr ht
  · intro hx
    change 1 < x at hx
    exact ⟨Real.log x, Real.log_pos hx, Real.exp_log (by linarith)⟩

lemma exp_cpow (t : ℝ) (s : ℂ) :
    (Real.exp t : ℂ) ^ s = Complex.exp ((t : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne')]
  rw [← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

lemma mangoldt_laplace_representation {z : ℂ} (hz : 0 < z.re) :
    LSeries (fun n => (Λ n : ℂ)) (1 + z) = (1 + z) *
      ∫ t in Ioi (0 : ℝ), Complex.exp (-z * t) * (normalizedPsi t : ℂ) := by
  rw [mangoldt_integral_representation (by simpa using hz)]
  congr 1
  rw [← exp_image_Ioi_zero,
    integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (Real.exp_monotone.monotoneOn _)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [exp_cpow]
  simp only [normalizedPsi, Complex.ofReal_mul, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_exp, Complex.ofReal_neg]
  rw [mul_comm (Complex.exp (-z * t)) (Complex.exp (-(t : ℂ)) * (Chebyshev.psi (Real.exp t) : ℂ))]
  simp only [← mul_assoc]
  have he : Complex.exp (t : ℂ) * Complex.exp ((t : ℂ) * -((1 + z) + 1)) =
      Complex.exp (-(t : ℂ)) * Complex.exp (-z * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (t : ℂ) * (Chebyshev.psi (Real.exp t) : ℂ) *
        Complex.exp ((t : ℂ) * -((1 + z) + 1)) =
      (Complex.exp (t : ℂ) * Complex.exp ((t : ℂ) * -((1 + z) + 1))) *
        (Chebyshev.psi (Real.exp t) : ℂ) := by ring
    _ = _ := by rw [he]; ring

lemma integrable_normalizedPsi_laplace {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * t) * (normalizedPsi t : ℂ)) (Ioi 0) := by
  have he := integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using neg_neg_of_pos hz) 0
  apply (he.norm.const_mul (Real.log 4 + 4)).mono'
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z * t))).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.measurable.comp measurable_normalizedPsi).aestronglyMeasurable)
  filter_upwards with t
  simp only [Pi.mul_apply, Function.comp_def, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (normalizedPsi_nonneg t)]
  exact (mul_le_mul_of_nonneg_left (normalizedPsi_le t) (norm_nonneg (Complex.exp (-z * t)))).trans_eq (mul_comm _ _)

lemma normalizedPsi_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-z * t) * (normalizedPsi t - 1 : ℝ)) =
      (mangoldtAux (1 + z) - 1) / (1 + z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have h1z0 : 1 + z ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith
  have hs : 1 < (1 + z).re := by simpa using hz
  have hi : (∫ t in Ioi (0 : ℝ), Complex.exp (-z * t) * (normalizedPsi t : ℂ)) =
      LSeries (fun n => (Λ n : ℂ)) (1 + z) / (1 + z) := by
    rw [mangoldt_laplace_representation hz]
    field_simp
  have he : (∫ t in Ioi (0 : ℝ), Complex.exp (-z * t)) = 1 / z := by
    rw [integral_exp_mul_complex_Ioi (a := -z) (by simpa using neg_neg_of_pos hz)]
    simp
  simp only [Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one]
  rw [integral_sub (integrable_normalizedPsi_laplace hz)
    (integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using neg_neg_of_pos hz) 0), hi, he,
    mangoldtAux_eq hs]
  have heq : 1 + z - 1 = z := by ring
  rw [heq]
  field_simp
  ring

noncomputable def laplaceBoundary (v : ℝ × ℝ) : ℂ :=
  let z : ℂ := (v.1 : ℂ) + (2 * Real.pi * v.2 : ℝ) * Complex.I
  (mangoldtAux (1 + z) - 1) / (1 + z)

lemma continuousOn_laplaceBoundary :
    ContinuousOn laplaceBoundary {v | 0 ≤ v.1 ∧ v.1 ≤ 1} := by
  let s : ℝ × ℝ → ℂ := fun v => 1 + ((v.1 : ℂ) + (2 * Real.pi * v.2 : ℝ) * Complex.I)
  have hc : Continuous s := by dsimp [s]; fun_prop
  have hs : ∀ v ∈ {v : ℝ × ℝ | 0 ≤ v.1 ∧ v.1 ≤ 1}, 1 ≤ (s v).re := by
    intro v hv
    simp only [s, Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    linarith [hv.1]
  apply ((continuousOn_mangoldtAux.comp hc.continuousOn hs).sub continuousOn_const).div hc.continuousOn
  intro v hv he
  have hh := hs v hv
  have hh' : (1 : ℝ) ≤ 0 := by simpa [he] using hh
  norm_num at hh'

/-- The normalized Chebyshev `ψ` function tends to one on logarithmic scale. -/
theorem normalizedPsi_tendsto : Tendsto normalizedPsi atTop (𝓝 1) := by
  apply bounded_laplace_tauberian measurable_normalizedPsi normalizedPsi_nonneg
    (fun _ ht => normalizedPsi_zero ht) (Real.log 4 + 4)
    (by have := Real.log_pos (show (1 : ℝ) < 4 by norm_num); linarith)
    normalizedPsi_le monotone_exp_mul_normalizedPsi laplaceBoundary continuousOn_laplaceBoundary
  intro ε ξ hε _
  apply normalizedPsi_laplace
  simpa using hε

/-- The prime number theorem in Chebyshev-`ψ` form. -/
theorem psi_div_self_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have h := normalizedPsi_tendsto.comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, normalizedPsi, Real.exp_neg, Real.exp_log hx]
  rw [div_eq_mul_inv, mul_comm]

lemma psi_sub_theta_div_tendsto :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  simp_rw [← Real.sqrt_eq_rpow] at hlog
  have hlim : Tendsto (fun x : ℝ => 2 * (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
    simpa using hlog.const_mul 2
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x)) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have h := (le_abs_self (Chebyshev.psi x - Chebyshev.theta x)).trans
      (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx)
    have hb := div_le_div_of_nonneg_right h hx0.le
    apply hb.trans_eq
    field_simp
    rw [Real.sq_sqrt hx0.le, mul_comm]

/-- The prime number theorem in Chebyshev-`θ` form. -/
theorem theta_div_self_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have h := psi_div_self_tendsto.sub psi_sub_theta_div_tendsto
  have he (x : ℝ) : Chebyshev.psi x / x - (Chebyshev.psi x - Chebyshev.theta x) / x =
      Chebyshev.theta x / x := by ring
  simpa only [he, sub_zero] using h

lemma theta_scaled_div_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Chebyshev.theta (a * x) / x) atTop (𝓝 a) := by
  have h := (theta_div_self_tendsto.comp (tendsto_id.const_mul_atTop ha)).const_mul a
  have he (x : ℝ) : a * (Chebyshev.theta (a * x) / (a * x)) =
      Chebyshev.theta (a * x) / x := by
    rw [← mul_div_assoc, mul_div_mul_left _ _ ha.ne']
  simpa only [Function.comp_def, id_eq, he, mul_one] using h

/-- Every fixed proportional interval has the expected logarithmic prime mass. -/
theorem theta_interval_div_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (Chebyshev.theta (b * x) - Chebyshev.theta (a * x)) / x)
      atTop (𝓝 (b - a)) := by
  simpa only [sub_div] using (theta_scaled_div_tendsto hb).sub (theta_scaled_div_tendsto ha)

/-- The local lower estimate needed to localize the metric first moment. -/
theorem eventually_theta_interval_lower {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, (b - a) / 2 * x ≤ Chebyshev.theta (b * x) - Chebyshev.theta (a * x) := by
  have h := (tendsto_order.mp (theta_interval_div_tendsto ha (ha.trans hab))).1
    ((b - a) / 2) (by linarith)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  exact ((lt_div_iff₀ hx0).mp hx).le

#print axioms psi_div_self_tendsto
#print axioms theta_div_self_tendsto
#print axioms eventually_theta_interval_lower

end Erdos972ChebyshevPNT
