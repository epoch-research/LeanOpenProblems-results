import Submission.PositiveBandKernel

/-! Removing band-limited smoothing for bounded functions whose exponential
multiple is monotone. -/
namespace Erdos972TauberianDesmoothing

open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap

lemma exp_monotone_comparison {f : ℝ → ℝ}
    (hm : Monotone (fun t => Real.exp t * f t)) {x y : ℝ} (hxy : x ≤ y) :
    f x ≤ Real.exp (y - x) * f y := by
  have h := mul_le_mul_of_nonneg_left (hm hxy) (Real.exp_pos (-x)).le
  have hx : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hy : Real.exp (-x) * Real.exp y = Real.exp (y - x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc, hx, one_mul, hy] using h

lemma forward_comparison {f : ℝ → ℝ} {M δ : ℝ}
    (hM : ∀ t, f t ≤ M) (hf : ∀ t, 0 ≤ f t)
    (hm : Monotone (fun t => Real.exp t * f t)) (hδ : 0 ≤ δ)
    {x t : ℝ} (hxt : x ≤ t) (ht : t ≤ x + 2 * δ) :
    f x ≤ f t + M * (Real.exp (2 * δ) - 1) := by
  have h := exp_monotone_comparison hm hxt
  have he : Real.exp (t - x) ≤ Real.exp (2 * δ) := Real.exp_le_exp.mpr (by linarith)
  have ha : 0 ≤ Real.exp (2 * δ) - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have h₁ := mul_le_mul_of_nonneg_right he (hf t)
  have h₂ := mul_le_mul_of_nonneg_right (hM t) ha
  nlinarith

lemma backward_comparison {f : ℝ → ℝ} {M δ : ℝ}
    (hM : ∀ t, f t ≤ M) (hf : ∀ t, 0 ≤ f t)
    (hm : Monotone (fun t => Real.exp t * f t)) (hδ : 0 ≤ δ)
    {x t : ℝ} (htx : t ≤ x) (ht : x - 2 * δ ≤ t) :
    f t ≤ f x + M * (Real.exp (2 * δ) - 1) := by
  have h := exp_monotone_comparison hm htx
  have he : Real.exp (x - t) ≤ Real.exp (2 * δ) := Real.exp_le_exp.mpr (by linarith)
  have ha : 0 ≤ Real.exp (2 * δ) - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have h₁ := mul_le_mul_of_nonneg_right he (hf x)
  have h₂ := mul_le_mul_of_nonneg_right (hM x) ha
  nlinarith

lemma integrable_average {f k : ℝ → ℝ} (hf : Measurable f) (hk : Integrable k)
    (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (x : ℝ) :
    Integrable (fun u => f (x + u) * k u) := by
  apply (hk.norm.const_mul M).mono'
    ((hf.comp (measurable_const.add measurable_id)).aestronglyMeasurable.mul hk.aestronglyMeasurable)
  filter_upwards with u
  simp only [Pi.mul_apply, Function.comp_def, id_eq, norm_mul]
  exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

/-- Upper and lower estimates from one-sided monotonicity and a concentrated
positive kernel. -/
lemma average_sandwich {f k : ℝ → ℝ} {M δ : ℝ}
    (hf : Measurable f) (hpos : ∀ t, 0 ≤ f t) (hM : ∀ t, f t ≤ M)
    (hm : Monotone (fun t => Real.exp t * f t)) (hδ : 0 < δ)
    (hk : Integrable k) (hkpos : ∀ t, 0 ≤ k t) (hkmass : (∫ t, k t) = 1) (x : ℝ) :
    f x ≤ (∫ u, f (x + δ + u) * k u) + M * (Real.exp (2 * δ) - 1) +
        M * (∫ u in (Ioo (-δ) δ)ᶜ, k u) ∧
    (∫ u, f (x - δ + u) * k u) ≤ f x + M * (Real.exp (2 * δ) - 1) +
        M * (∫ u in (Ioo (-δ) δ)ᶜ, k u) := by
  let E := M * (Real.exp (2 * δ) - 1)
  have hM0 : 0 ≤ M := (hpos 0).trans (hM 0)
  have hE : 0 ≤ E := mul_nonneg hM0 (sub_nonneg.mpr
    (Real.one_le_exp_iff.mpr (by positivity)))
  have hbound (t : ℝ) : ‖f t‖ ≤ M := by simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos t)] using hM t
  have htail : Integrable ((Ioo (-δ) δ)ᶜ.indicator k) := hk.indicator measurableSet_Ioo.compl
  have hPlus := integrable_average hf hk M hbound (x + δ)
  have hMinus := integrable_average hf hk M hbound (x - δ)
  have hp (u : ℝ) :
      f x * k u ≤ f (x + δ + u) * k u + E * k u +
        M * (Ioo (-δ) δ)ᶜ.indicator k u := by
    by_cases hu : u ∈ Ioo (-δ) δ
    · rw [Set.indicator_of_notMem (show u ∉ (Ioo (-δ) δ)ᶜ by simpa using hu), mul_zero, add_zero]
      have h := forward_comparison hM hpos hm hδ.le
        (x := x) (t := x + δ + u) (by linarith [hu.1]) (by linarith [hu.2])
      simpa only [E, add_mul] using mul_le_mul_of_nonneg_right h (hkpos u)
    · rw [Set.indicator_of_mem hu]
      have h := mul_le_mul_of_nonneg_right (hM x) (hkpos u)
      have h₁ := mul_nonneg (hpos (x + δ + u)) (hkpos u)
      have h₂ := mul_nonneg hE (hkpos u)
      linarith
  have hn (u : ℝ) :
      f (x - δ + u) * k u ≤ f x * k u + E * k u +
        M * (Ioo (-δ) δ)ᶜ.indicator k u := by
    by_cases hu : u ∈ Ioo (-δ) δ
    · rw [Set.indicator_of_notMem (show u ∉ (Ioo (-δ) δ)ᶜ by simpa using hu), mul_zero, add_zero]
      have h := backward_comparison hM hpos hm hδ.le
        (x := x) (t := x - δ + u) (by linarith [hu.2]) (by linarith [hu.1])
      simpa only [E, add_mul] using mul_le_mul_of_nonneg_right h (hkpos u)
    · rw [Set.indicator_of_mem hu]
      have h := mul_le_mul_of_nonneg_right (hM (x - δ + u)) (hkpos u)
      have h₁ := mul_nonneg (hpos x) (hkpos u)
      have h₂ := mul_nonneg hE (hkpos u)
      linarith
  have hpi := integral_mono (hk.const_mul (f x))
    ((hPlus.add (hk.const_mul E)).add (htail.const_mul M)) hp
  have hni := integral_mono hMinus
    (((hk.const_mul (f x)).add (hk.const_mul E)).add (htail.const_mul M)) hn
  simp only [Pi.add_apply] at hpi hni
  rw [integral_add (f := fun u => f (x + δ + u) * k u + E * k u) (hPlus.add (hk.const_mul E)) (htail.const_mul M),
    integral_add hPlus (hk.const_mul E)] at hpi
  rw [integral_add (f := fun u => f x * k u + E * k u) ((hk.const_mul (f x)).add (hk.const_mul E)) (htail.const_mul M),
    integral_add (hk.const_mul (f x)) (hk.const_mul E)] at hni
  simp only [integral_const_mul, integral_indicator measurableSet_Ioo.compl, hkmass, mul_one] at hpi hni
  exact ⟨hpi, hni⟩

/-- A bounded nonnegative function with monotone exponential multiple is
determined pointwise at infinity by all its band-limited Schwartz averages. -/
theorem tendsto_of_schwartz_averages {f : ℝ → ℝ} (hf : Measurable f)
    (hpos : ∀ t, 0 ≤ f t) (M : ℝ) (hM0 : 0 < M) (hM : ∀ t, f t ≤ M)
    (hm : Monotone (fun t => Real.exp t * f t))
    (hAvg : ∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) →
      Tendsto (fun x => ∫ u, f (x + u) * (𝓕 φ u).re) atTop
        (𝓝 (∫ u, (𝓕 φ u).re))) :
    Tendsto f atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (4 * M)
  have hη : 0 < η := by dsimp [η]; positivity
  let δ : ℝ := Real.log (1 + η) / 2
  have hδ : 0 < δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have hE : M * (Real.exp (2 * δ) - 1) = ε / 4 := by
    have hd : 2 * δ = Real.log (1 + η) := by dsimp [δ]; ring
    rw [hd, Real.exp_log (by linarith : 0 < 1 + η)]
    dsimp [η]
    field_simp
    ring
  have hηM : M * η = ε / 4 := by dsimp [η]; field_simp
  obtain ⟨φ, hφ, hkpos, _, hkmass, hktail⟩ :=
    Erdos972PositiveBandKernel.exists_concentrated_positive_kernel hδ hη
  have ha := hAvg φ hφ
  rw [hkmass] at ha
  have haPlus := ha.comp (tendsto_atTop_add_const_right atTop δ tendsto_id)
  have haMinus := ha.comp (by simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-δ) tendsto_id)
  have hp := (Metric.tendsto_nhds.mp haPlus) (ε / 4) (by positivity)
  have hn := (Metric.tendsto_nhds.mp haMinus) (ε / 4) (by positivity)
  filter_upwards [hp, hn] with x hxp hxn
  have hs := average_sandwich hf hpos hM hm hδ (𝓕 φ).integrable.re hkpos hkmass x
  rw [hE] at hs
  have htail := mul_lt_mul_of_pos_left hktail hM0
  rw [hηM] at htail
  simp only [Function.comp_def, id_eq, ← sub_eq_add_neg, dist_eq_norm, Real.norm_eq_abs] at hxp hxn ⊢
  obtain ⟨hp₁, hp₂⟩ := abs_lt.mp hxp
  obtain ⟨hn₁, hn₂⟩ := abs_lt.mp hxn
  apply abs_lt.mpr
  constructor <;> linarith [hs.1, hs.2]

#print axioms tendsto_of_schwartz_averages

end Erdos972TauberianDesmoothing
