import Submission.Elliptic

open Set Filter MeasureTheory intervalIntegral
open scoped BigOperators Interval

namespace Elliptic

noncomputable def Ki (m : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ),
    (Real.sqrt ((1+t^2) * (1+(1-m)*t^2)))⁻¹

noncomputable def Ei (m : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ),
    Real.sqrt (1+(1-m)*t^2) / (Real.sqrt (1+t^2))^3

lemma tangent_K_integrand_continuous {m : ℝ} (hm : m < 1) : Continuous
    (fun t : ℝ => (Real.sqrt ((1+t^2)*(1+(1-m)*t^2)))⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro t
    apply (Real.sqrt_pos.2 ?_).ne'
    exact mul_pos (by positivity) (by nlinarith [sq_nonneg t, mul_nonneg (sub_pos.2 hm).le (sq_nonneg t)])

lemma tangent_E_integrand_continuous {m : ℝ} (hm : m ≤ 1) : Continuous
    (fun t : ℝ => Real.sqrt (1+(1-m)*t^2) / Real.sqrt (1+t^2)^3) := by
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro t
    exact pow_ne_zero _ (Real.sqrt_pos.2 (by positivity)).ne'

lemma integrableOn_Ki {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    IntegrableOn (fun t : ℝ =>
      (Real.sqrt ((1+t^2)*(1+(1-m)*t^2)))⁻¹) (Ioi 0) := by
  have hc : 0 < Real.sqrt (1-m) := Real.sqrt_pos.2 (sub_pos.2 hm1)
  have hg : Integrable (fun t : ℝ => (Real.sqrt (1-m))⁻¹ * (1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply hg.integrableOn.mono' (tangent_K_integrand_continuous hm1).aestronglyMeasurable
  filter_upwards [] with t
  have hfac : (1-m)*(1+t^2) ≤ 1+(1-m)*t^2 := by nlinarith
  have hmul : (1-m)*(1+t^2)^2 ≤ (1+t^2)*(1+(1-m)*t^2) := by
    calc
      (1-m)*(1+t^2)^2 = (1+t^2)*((1-m)*(1+t^2)) := by ring
      _ ≤ (1+t^2)*(1+(1-m)*t^2) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
  have hsqrt := Real.sqrt_le_sqrt hmul
  have hsprod : Real.sqrt ((1-m)*(1+t^2)^2) = Real.sqrt (1-m)*(1+t^2) := by
    rw [Real.sqrt_mul (sub_nonneg.2 hm1.le), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1+t^2)]
  rw [hsprod] at hsqrt
  rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    (Real.sqrt ((1+t^2)*(1+(1-m)*t^2)))⁻¹ ≤
        (Real.sqrt (1-m)*(1+t^2))⁻¹ :=
      inv_anti₀ (mul_pos hc (by positivity)) hsqrt
    _ = (Real.sqrt (1-m))⁻¹ * (1+t^2)⁻¹ := by
      rw [mul_inv_rev]
      ring

lemma integrableOn_Ei {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    IntegrableOn (fun t : ℝ =>
      Real.sqrt (1+(1-m)*t^2) / Real.sqrt (1+t^2)^3) (Ioi 0) := by
  apply integrable_inv_one_add_sq.integrableOn.mono'
    (tangent_E_integrand_continuous hm1).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hr0 : 0 ≤ 1+(1-m)*t^2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hm1) (sq_nonneg t)]
  have hr : 1+(1-m)*t^2 ≤ 1+t^2 := by nlinarith [mul_nonneg hm0 (sq_nonneg t)]
  have hs := Real.sqrt_le_sqrt hr
  have hbase : 0 < Real.sqrt (1+t^2) := Real.sqrt_pos.2 (by positivity)
  rw [show (1+t^2) = Real.sqrt (1+t^2)^2 by
    rw [Real.sq_sqrt (by positivity)]
  , Real.sqrt_sq hbase.le]
  field_simp [hbase.ne']
  exact hs


lemma Ki_tan_pointwise {m x : ℝ} (hm : m < 1) (hcos : 0 < Real.cos x) :
    (Real.sqrt ((1+Real.tan x^2)*(1+(1-m)*Real.tan x^2)))⁻¹ *
        (1/Real.cos x^2) =
      (Real.sqrt (1-m*Real.sin x^2))⁻¹ := by
  have hc := hcos.ne'
  have hr := radicand_pos hm x
  have hprod : (1+Real.tan x^2)*(1+(1-m)*Real.tan x^2) =
      (1-m*Real.sin x^2) / Real.cos x^4 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hprod, Real.sqrt_div hr.le (Real.cos x^4)]
  have hsqrtcos : Real.sqrt (Real.cos x^4) = Real.cos x^2 := by
    rw [show Real.cos x^4 = (Real.cos x^2)^2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hsqrtcos]
  field_simp [hc, (Real.sqrt_pos.2 hr).ne']

lemma Ei_tan_pointwise {m x : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hcos : 0 < Real.cos x) :
    (Real.sqrt (1+(1-m)*Real.tan x^2) / Real.sqrt (1+Real.tan x^2)^3) *
        (1/Real.cos x^2) = Real.sqrt (1-m*Real.sin x^2) := by
  have hc := hcos.ne'
  have hr : 0 ≤ 1-m*Real.sin x^2 := by
    nlinarith [mul_le_mul_of_nonneg_left (sin_sq_le_one x) hm0]
  have h1 : 1+Real.tan x^2 = 1/Real.cos x^2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h2 : 1+(1-m)*Real.tan x^2 =
      (1-m*Real.sin x^2)/Real.cos x^2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [h1, h2, Real.sqrt_div hr (Real.cos x^2),
    Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) (Real.cos x^2),
    Real.sqrt_sq_eq_abs, abs_of_pos hcos]
  field_simp [hc]
  norm_num


lemma K_eq_Ki {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) : K m = Ki m := by
  let f : ℝ → ℝ := fun x => (Real.sqrt (1-m*Real.sin x^2))⁻¹
  let g : ℝ → ℝ := fun t =>
    (Real.sqrt ((1+t^2)*(1+(1-m)*t^2)))⁻¹
  let l : Filter ℝ := nhdsWithin (Real.pi/2) (Iio (Real.pi/2))
  have hleft : Tendsto (fun b : ℝ => ∫ x in (0:ℝ)..b, f x) l (nhds (K m)) := by
    have hp : ContinuousAt (fun b : ℝ => ∫ x in (0:ℝ)..b, f x) (Real.pi/2) := by
      apply HasDerivAt.continuousAt
      apply intervalIntegral.integral_hasDerivAt_right
      · exact (continuous_K_integrand hm1).intervalIntegrable _ _
      · exact (continuous_K_integrand hm1).stronglyMeasurableAtFilter volume _
      · exact (continuous_K_integrand hm1).continuousAt
    have hi : Tendsto (fun x : ℝ => x) l (nhds (Real.pi/2)) :=
      tendsto_id.mono_left inf_le_left
    simpa [K, f] using hp.tendsto.comp hi
  have hright : Tendsto (fun b : ℝ => ∫ t in (0:ℝ)..Real.tan b, g t) l
      (nhds (Ki m)) := by
    simpa [Ki, g, l] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (f := g) 0
        (by simpa [g] using integrableOn_Ki hm0 hm1)
        Real.tendsto_tan_pi_div_two)
  have heq : ∀ᶠ b in l,
      (∫ x in (0:ℝ)..b, f x) = ∫ t in (0:ℝ)..Real.tan b, g t := by
    have hev : Ioo (0:ℝ) (Real.pi/2) ∈ l := by
      simpa [l] using (Ioo_mem_nhdsLT (by positivity : (0:ℝ) < Real.pi/2))
    filter_upwards [hev] with b hb
    have hcos : ∀ x ∈ uIcc (0:ℝ) b, 0 < Real.cos x := by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) b := by simpa [uIcc_of_le hb.1.le] using hx
      exact Real.cos_pos_of_mem_Ioo ⟨
        lt_of_lt_of_le (neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num))) hx'.1,
        lt_of_le_of_lt hx'.2 hb.2⟩
    have hsub := intervalIntegral.integral_comp_mul_deriv
      (f := Real.tan) (f' := fun x => 1/Real.cos x^2) (g := g)
      (fun x hx => Real.hasDerivAt_tan (hcos x hx).ne')
      (by
        apply ContinuousOn.div continuousOn_const (Real.continuous_cos.pow 2).continuousOn
        intro x hx
        exact pow_ne_zero _ (hcos x hx).ne')
      (tangent_K_integrand_continuous hm1)
    rw [Real.tan_zero] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro x hx
    exact (Ki_tan_pointwise hm1 (hcos x hx)).symm
  have := tendsto_nhds_unique (hleft.congr' heq) hright
  exact this


lemma E_eq_Ei {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) : E m = Ei m := by
  let f : ℝ → ℝ := fun x => Real.sqrt (1-m*Real.sin x^2)
  let g : ℝ → ℝ := fun t =>
    Real.sqrt (1+(1-m)*t^2) / Real.sqrt (1+t^2)^3
  let l : Filter ℝ := nhdsWithin (Real.pi/2) (Iio (Real.pi/2))
  have hleft : Tendsto (fun b : ℝ => ∫ x in (0:ℝ)..b, f x) l (nhds (E m)) := by
    have hp : ContinuousAt (fun b : ℝ => ∫ x in (0:ℝ)..b, f x) (Real.pi/2) := by
      apply HasDerivAt.continuousAt
      apply intervalIntegral.integral_hasDerivAt_right
      · exact (continuous_E_integrand m).intervalIntegrable _ _
      · exact (continuous_E_integrand m).stronglyMeasurableAtFilter volume _
      · exact (continuous_E_integrand m).continuousAt
    have hi : Tendsto (fun x : ℝ => x) l (nhds (Real.pi/2)) :=
      tendsto_id.mono_left inf_le_left
    simpa [E, f] using hp.tendsto.comp hi
  have hright : Tendsto (fun b : ℝ => ∫ t in (0:ℝ)..Real.tan b, g t) l
      (nhds (Ei m)) := by
    simpa [Ei, g, l] using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (f := g) 0
        (by simpa [g] using integrableOn_Ei hm0 hm1)
        Real.tendsto_tan_pi_div_two)
  have heq : ∀ᶠ b in l,
      (∫ x in (0:ℝ)..b, f x) = ∫ t in (0:ℝ)..Real.tan b, g t := by
    have hev : Ioo (0:ℝ) (Real.pi/2) ∈ l := by
      simpa [l] using (Ioo_mem_nhdsLT (by positivity : (0:ℝ) < Real.pi/2))
    filter_upwards [hev] with b hb
    have hcos : ∀ x ∈ uIcc (0:ℝ) b, 0 < Real.cos x := by
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) b := by simpa [uIcc_of_le hb.1.le] using hx
      exact Real.cos_pos_of_mem_Ioo ⟨
        lt_of_lt_of_le (neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num))) hx'.1,
        lt_of_le_of_lt hx'.2 hb.2⟩
    have hsub := intervalIntegral.integral_comp_mul_deriv
      (f := Real.tan) (f' := fun x => 1/Real.cos x^2) (g := g)
      (fun x hx => Real.hasDerivAt_tan (hcos x hx).ne')
      (by
        apply ContinuousOn.div continuousOn_const (Real.continuous_cos.pow 2).continuousOn
        intro x hx
        exact pow_ne_zero _ (hcos x hx).ne')
      (tangent_E_integrand_continuous hm1)
    rw [Real.tan_zero] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro x hx
    exact (Ei_tan_pointwise hm0 hm1 (hcos x hx)).symm
  exact tendsto_nhds_unique (hleft.congr' heq) hright



end Elliptic
