import FormalConjecturesUtil

/-! Elementary triangular-integral identities used to analyze the continuous
radial sieve profile. These are analytic identities, not Jacobsthal bounds. -/
namespace Erdos970.RadialProfile
open MeasureTheory Set intervalIntegral

lemma integral_eq_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, f x) = ∫ x in Icc a b, f x := by
  rw [integral_of_le hab, integral_Icc_eq_integral_Ioc]

lemma integral_triangle_swap (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..1, ∫ y in x..1, f (x, y)) =
      ∫ y in (0 : ℝ)..1, ∫ x in 0..y, f (x, y) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 1)
  have hi : Integrable f (μ.prod μ) := by
    rw [show μ = volume.restrict (Icc (0 : ℝ) 1) from rfl,
      Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuousOn
  have hh : Integrable (fun z : ℝ × ℝ => if z.1 ≤ z.2 then f z else 0) (μ.prod μ) :=
    hi.indicator (measurableSet_le measurable_fst measurable_snd)
  have hs := integral_integral_swap (f := fun x y => if x ≤ y then f (x, y) else 0) hh
  have hl (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (∫ y, (if x ≤ y then f (x, y) else 0) ∂μ) = ∫ y in x..1, f (x, y) := by
    change (∫ y, (Ici x).indicator (fun y => f (x, y)) y ∂μ) = _
    rw [MeasureTheory.integral_indicator measurableSet_Ici]
    change (∫ y, f (x, y) ∂((volume.restrict (Icc 0 1)).restrict (Ici x))) = _
    rw [Measure.restrict_restrict measurableSet_Ici]
    have he : Ici x ∩ Icc (0 : ℝ) 1 = Icc x 1 := by
      ext y
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨hxy, hy0, hy1⟩; exact ⟨hxy, hy1⟩
      · rintro ⟨hxy, hy1⟩; exact ⟨hxy, hx.1.trans hxy, hy1⟩
    rw [he, integral_eq_Icc hx.2]
  have hr (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      (∫ x, (if x ≤ y then f (x, y) else 0) ∂μ) = ∫ x in 0..y, f (x, y) := by
    change (∫ x, (Iic y).indicator (fun x => f (x, y)) x ∂μ) = _
    rw [MeasureTheory.integral_indicator measurableSet_Iic]
    change (∫ x, f (x, y) ∂((volume.restrict (Icc 0 1)).restrict (Iic y))) = _
    rw [Measure.restrict_restrict measurableSet_Iic]
    have he : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 y := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxy, hx0, hx1⟩; exact ⟨hx0, hxy⟩
      · rintro ⟨hx0, hxy⟩; exact ⟨hxy, hx0, hxy.trans hy.2⟩
    rw [he, integral_eq_Icc hy.1]
  rw [integral_eq_Icc (by norm_num), integral_eq_Icc (by norm_num)]
  calc
    _ = ∫ x, ∫ y, (if x ≤ y then f (x, y) else 0) ∂μ ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact (hl x hx).symm
    _ = ∫ y, ∫ x, (if x ≤ y then f (x, y) else 0) ∂μ ∂μ := hs
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      exact hr y hy

lemma primitive_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun u => ∫ v in (0 : ℝ)..u, f v) :=
  continuous_primitive (fun a b => hf.intervalIntegrable a b) 0

lemma primitive_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (u : ℝ) :
    HasDerivAt (fun x => ∫ v in (0 : ℝ)..x, f v) (f u) u :=
  integral_hasDerivAt_right (hf.intervalIntegrable 0 u)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

lemma integral_prefix (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ u in (0 : ℝ)..1, ∫ v in 0..u, f v) = ∫ u in (0 : ℝ)..1, (1 - u) * f u := by
  have hd (u : ℝ) : HasDerivAt (fun x => x * ∫ v in (0 : ℝ)..x, f v)
      ((∫ v in (0 : ℝ)..u, f v) + u * f u) u := by
    simpa only [one_mul] using (hasDerivAt_id u).mul (primitive_hasDerivAt f hf u)
  have hc : Continuous (fun u => (∫ v in (0 : ℝ)..u, f v) + u * f u) :=
    (primitive_continuous f hf).add (continuous_id.mul hf)
  have h := integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hc.intervalIntegrable 0 1)
  have him : IntervalIntegrable (fun u : ℝ => u * f u) volume 0 1 :=
    (show Continuous (fun u : ℝ => u * f u) by fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (primitive_continuous f hf |>.intervalIntegrable 0 1) him] at h
  simp only [one_mul, integral_same, mul_zero, sub_zero] at h
  have he (u : ℝ) : (1 - u) * f u = f u - u * f u := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 1) him]
  linarith

lemma integral_triangle_square (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ u in (0 : ℝ)..1, ∫ v in 0..u, (f u - f v) ^ 2) =
      (∫ u in (0 : ℝ)..1, f u ^ 2) - (∫ u in (0 : ℝ)..1, f u) ^ 2 := by
  let A : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, f v
  let B : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, f v ^ 2
  have hA : Continuous A := primitive_continuous f hf
  have hB : Continuous B := primitive_continuous (fun u => f u ^ 2) (hf.pow 2)
  have hi (u : ℝ) : (∫ v in (0 : ℝ)..u, (f u - f v) ^ 2) =
      u * f u ^ 2 + B u - 2 * f u * A u := by
    have he (v : ℝ) : (f u - f v) ^ 2 = (f u) ^ 2 + f v ^ 2 - (2 * f u) * f v := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp only [sub_zero, smul_eq_mul, A, B]
    · exact continuous_const.intervalIntegrable 0 u
    · exact (hf.pow 2).intervalIntegrable 0 u
    · exact (continuous_const.add (hf.pow 2)).intervalIntegrable 0 u
    · exact (continuous_const.mul hf).intervalIntegrable 0 u
  have hd (u : ℝ) : HasDerivAt (fun x => x * B x - A x ^ 2)
      (u * f u ^ 2 + B u - 2 * f u * A u) u := by
    have hBu := primitive_hasDerivAt (fun v => f v ^ 2) (hf.pow 2) u
    have hAu := primitive_hasDerivAt f hf u
    convert ((hasDerivAt_id u).mul hBu).sub (hAu.pow 2) using 1 <;> dsimp [A, B] <;> ring
  have hc : Continuous (fun u => u * f u ^ 2 + B u - 2 * f u * A u) := by fun_prop
  simp_rw [hi]
  have h := integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hc.intervalIntegrable 0 1)
  simpa only [A, B, one_mul, integral_same, mul_zero, zero_pow (by omega : 2 ≠ 0),
    sub_zero, zero_sub] using h

lemma shift_inner_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun v : ℝ => ∫ u in v..1, (f u - f (u - v)) ^ 2) := by
  have hj : Continuous (Function.uncurry (fun v u : ℝ => (f u - f (u - v)) ^ 2)) := by
    fun_prop
  have h1 := continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hj 0 1
  have h2 := continuous_parametric_intervalIntegral_of_continuous (μ := volume)
    (a₀ := 0) hj continuous_id'
  convert h1.sub h2 using 1
  funext v
  have hu : Continuous (fun u : ℝ => (f u - f (u - v)) ^ 2) := by fun_prop
  exact (integral_interval_sub_left (hu.intervalIntegrable 0 1)
    (hu.intervalIntegrable 0 v)).symm

/-- The unweighted split-shift energy is a variance plus an endpoint term. -/
theorem unweighted_split_shift_integral (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ v in (0 : ℝ)..1,
      (∫ u in v..1, (f u - f (u - v)) ^ 2) + ∫ u in 0..v, f u ^ 2) =
      (∫ u in (0 : ℝ)..1, f u ^ 2) - (∫ u in (0 : ℝ)..1, f u) ^ 2 +
      ∫ u in (0 : ℝ)..1, (1 - u) * f u ^ 2 := by
  have hc := shift_inner_continuous f hf
  rw [intervalIntegral.integral_add (hc.intervalIntegrable 0 1)
    ((primitive_continuous (fun u => f u ^ 2) (hf.pow 2)).intervalIntegrable 0 1),
    integral_prefix _ (hf.pow 2)]
  congr 1
  rw [integral_triangle_swap (fun z : ℝ × ℝ => (f z.2 - f (z.2 - z.1)) ^ 2) (by fun_prop)]
  have he (u : ℝ) : (∫ v in (0 : ℝ)..u, (f u - f (u - v)) ^ 2) =
      ∫ v in (0 : ℝ)..u, (f u - f v) ^ 2 := by
    simpa only [sub_self, sub_zero] using integral_comp_sub_left (a := 0) (b := u) (fun v => (f u - f v) ^ 2) u
  simp_rw [he]
  exact integral_triangle_square f hf

#print axioms unweighted_split_shift_integral
end Erdos970.RadialProfile
