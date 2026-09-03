import Submission.FourierBoundaryConvolution

/-! The bounded half-line Laplace setup for the Fourier-boundary criterion.
A continuous closed-strip extension yields actual band-limited convolution
decay. The monotone Tauberian squeeze and arithmetic specialization are not
asserted here. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform
open scoped Topology
set_option autoImplicit false

noncomputable def dampingScale (n : ℕ) : ℝ := 1/((n : ℝ)+1)

lemma dampingScale_pos (n : ℕ) : 0 < dampingScale n := by
  unfold dampingScale
  positivity

lemma dampingScale_le_one (n : ℕ) : dampingScale n ≤ 1 := by
  unfold dampingScale
  exact (div_le_one (by positivity : (0 : ℝ) < n+1)).mpr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

lemma dampingScale_zero : Tendsto dampingScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma compact_strip_fourier_limit
    (fₙ : ℕ → ℝ → ℂ) (F : ℝ × ℝ → ℂ) (ψ : ℝ → ℂ)
    (hF : ContinuousOn F ((Set.Icc 0 1) ×ˢ Set.univ))
    (hEq : ∀ n ξ, 𝓕 (fₙ n) ξ = F (dampingScale n,ξ))
    (hc : HasCompactSupport ψ) :
    (∀ ξ, Tendsto (fun n => 𝓕 (fₙ n) ξ) atTop (𝓝 (F (0,ξ)))) ∧
    ∃ B : ℝ, ∀ n ξ, ψ ξ ≠ 0 → ‖𝓕 (fₙ n) ξ‖ ≤ B := by
  constructor
  · intro ξ
    simp_rw [hEq]
    apply (hF (0,ξ) (by simp)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨dampingScale_zero.prodMk_nhds tendsto_const_nhds,?_⟩
    exact Eventually.of_forall (fun n => ⟨⟨(dampingScale_pos n).le,dampingScale_le_one n⟩,Set.mem_univ _⟩)
  · obtain ⟨B,hB⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn
      (hF.mono (Set.prod_mono_right (Set.subset_univ _)))
    refine ⟨B,?_⟩
    intro n ξ hξ
    rw [hEq]
    exact hB _ ⟨⟨(dampingScale_pos n).le,dampingScale_le_one n⟩,subset_tsupport ψ hξ⟩

noncomputable def damped (f : ℝ → ℂ) (σ t : ℝ) : ℂ :=
  (Real.exp (-σ*t) : ℂ)*f t

lemma damped_measurable (f : ℝ → ℂ) (hf : AEStronglyMeasurable f) (σ : ℝ) :
    AEStronglyMeasurable (damped f σ) := by
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable.mul hf

lemma norm_damped (f : ℝ → ℂ) (σ t : ℝ) :
    ‖damped f σ t‖ = Real.exp (-σ*t)*‖f t‖ := by
  simp only [damped,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

lemma norm_damped_le (f : ℝ → ℂ) (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M)
    (hsupp : ∀ t, t < 0 → f t = 0) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ) :
    ‖damped f σ t‖ ≤ M := by
  by_cases ht : 0 ≤ t
  · rw [norm_damped]
    have he : Real.exp (-σ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa using hM t)
  · simp only [damped,hsupp t (by linarith),mul_zero,norm_zero]
    exact (norm_nonneg (f t)).trans (hM t)

lemma integrable_damped (f : ℝ → ℂ) (hf : AEStronglyMeasurable f)
    (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M)
    (hsupp : ∀ t, t < 0 → f t = 0) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (damped f σ) := by
  have he : Integrable ((Set.Ici 0).indicator (fun t : ℝ => Real.exp (-σ*t))) := by
    rw [integrable_indicator_iff measurableSet_Ici]
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    exact integrableOn_exp_mul_Ioi (by linarith : -σ < 0) 0
  apply (he.const_mul M).mono' (damped_measurable f hf σ)
  apply Eventually.of_forall
  intro t
  by_cases ht : 0 ≤ t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ici (0 : ℝ) from ht),norm_damped]
    calc
      _ ≤ Real.exp (-σ*t)*M := mul_le_mul_of_nonneg_left (hM t) (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · simp [Set.indicator_of_notMem (show t ∉ Set.Ici (0 : ℝ) from ht),damped,hsupp t (by linarith)]

lemma damped_tendsto (f : ℝ → ℂ) (t : ℝ) :
    Tendsto (fun n => damped f (dampingScale n) t) atTop (𝓝 (f t)) := by
  have he : Tendsto (fun n => Real.exp (-dampingScale n*t)) atTop (𝓝 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp (dampingScale_zero.neg.mul_const t)
  have hc := (Complex.continuous_ofReal.continuousAt.tendsto.comp he).mul_const (f t)
  simpa only [damped,Complex.ofReal_one,one_mul] using hc

/-- For a bounded measurable half-line function, a continuous Fourier--Laplace
extension to the closed strip implies decay against every integrable Fourier
kernel with an integrable, compactly supported frequency test. -/
theorem closed_strip_convolution_decay
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f)
    (M : ℝ) (hM : ∀ t, ‖f t‖ ≤ M) (hsupp : ∀ t, t < 0 → f t = 0)
    (F : ℝ × ℝ → ℂ) (hF : ContinuousOn F ((Set.Icc 0 1) ×ˢ Set.univ))
    (hEq : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∀ ξ, 𝓕 (damped f σ) ξ = F (σ,ξ))
    (ψ : ℝ → ℂ) (hc : HasCompactSupport ψ)
    (hψ : Integrable ψ) (hK : Integrable (𝓕 ψ)) :
    Integrable (fun ξ => F (0,ξ)*ψ ξ) ∧
    (∀ x, Integrable (fun t => f t*𝓕 ψ (t-x))) ∧
    Tendsto (fun x : ℝ => ∫ t, f t*𝓕 ψ (t-x)) atTop (𝓝 0) := by
  let fₙ := fun n => damped f (dampingScale n)
  obtain ⟨hl,B,hB⟩ := compact_strip_fourier_limit fₙ F ψ hF
    (fun n => hEq _ (dampingScale_pos n) (dampingScale_le_one n)) hc
  apply boundary_convolution_decay f fₙ (fun ξ => F (0,ξ)) ψ
    (fun n => integrable_damped f hf M hM hsupp _ (dampingScale_pos n)) M
    (fun n t => norm_damped_le f M hM hsupp _ (dampingScale_pos n).le t)
    (damped_tendsto f) hl B hB hψ hK

#print axioms closed_strip_convolution_decay
end Erdos371.FourierBoundary
