import FormalConjecturesUtil

/-! A dominated Fourier-boundary limit gives decay against band-limited
integrable kernels. This is a Tauberian ingredient, not an arithmetic prime
cancellation theorem. Every integral used below is genuinely integrable. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform
open scoped Topology
set_option autoImplicit false

lemma fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

lemma integral_fourier_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, 𝓕 f ξ * g ξ) = ∫ t, f t * 𝓕 g t := by
  simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg

noncomputable def modulate (x : ℝ) (ψ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  𝐞 (ξ*x) • ψ ξ

lemma integrable_modulate {ψ : ℝ → ℂ} (hψ : Integrable ψ) (x : ℝ) :
    Integrable (modulate x ψ) := by
  apply hψ.norm.mono'
  · exact ((Real.continuous_fourierChar.comp (continuous_id.mul continuous_const)).aestronglyMeasurable).smul hψ.1
  · exact Eventually.of_forall (fun ξ => by simp [modulate])

lemma norm_modulate (x ξ : ℝ) (ψ : ℝ → ℂ) : ‖modulate x ψ ξ‖ = ‖ψ ξ‖ := by
  simp [modulate]

lemma fourier_modulate (x t : ℝ) (ψ : ℝ → ℂ) :
    𝓕 (modulate x ψ) t = 𝓕 ψ (t-x) := by
  simp only [Real.fourier_real_eq,modulate,smul_smul,← AddChar.map_add_eq_mul]
  congr 1
  funext ξ
  congr 2
  ring

lemma fourierInv_eq_integral_modulate (x : ℝ) (G ψ : ℝ → ℂ) :
    𝓕⁻ (fun ξ => G ξ*ψ ξ) x = ∫ ξ, G ξ*modulate x ψ ξ := by
  rw [Real.fourierInv_eq]
  congr 1
  funext ξ
  simp only [modulate,Circle.smul_def,smul_eq_mul,real_inner_comm]
  change (𝐞 (ξ*x) : ℂ)*(G ξ*ψ ξ) = G ξ*((𝐞 (ξ*x) : ℂ)*ψ ξ)
  ring

lemma integrable_physical_pairing
    (f : ℝ → ℂ) (fₙ : ℕ → ℝ → ℂ) (ψ : ℝ → ℂ)
    (hfₙ : ∀ n, Integrable (fₙ n))
    (M : ℝ) (hM : ∀ n t, ‖fₙ n t‖ ≤ M)
    (hlim : ∀ t, Tendsto (fun n => fₙ n t) atTop (𝓝 (f t)))
    (hK : Integrable (𝓕 ψ)) (x : ℝ) :
    Integrable (fun t => f t * 𝓕 ψ (t-x)) := by
  have hfm : AEStronglyMeasurable f :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hfₙ n).1) (Eventually.of_forall hlim)
  apply (hK.comp_sub_right x).bdd_mul hfm
  exact Eventually.of_forall (fun t =>
    le_of_tendsto (hlim t).norm (Eventually.of_forall (fun n => hM n t)))

lemma integrable_frequency_pairing
    (fₙ : ℕ → ℝ → ℂ) (G ψ : ℝ → ℂ)
    (hfₙ : ∀ n, Integrable (fₙ n))
    (hFourier : ∀ ξ, Tendsto (fun n => 𝓕 (fₙ n) ξ) atTop (𝓝 (G ξ)))
    (B : ℝ) (hB : ∀ n ξ, ψ ξ ≠ 0 → ‖𝓕 (fₙ n) ξ‖ ≤ B)
    (hψ : Integrable ψ) : Integrable (fun ξ => G ξ*ψ ξ) := by
  have hGm : AEStronglyMeasurable G :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (fourier_continuous (hfₙ n)).aestronglyMeasurable)
      (Eventually.of_forall hFourier)
  apply (hψ.norm.const_mul B).mono' (hGm.mul hψ.1)
  apply Eventually.of_forall
  intro ξ
  change ‖G ξ*ψ ξ‖ ≤ B*‖ψ ξ‖
  by_cases hz : ψ ξ = 0
  · simp [hz]
  · rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact le_of_tendsto (hFourier ξ).norm (Eventually.of_forall (fun n => hB n ξ hz))

/-- A general bounded sequence of integrable approximants. The Fourier
transforms need only be uniformly bounded on the support of the test function.
Pointwise convergence is used on both sides, with two separate dominators. -/
theorem boundary_pairing
    (f : ℝ → ℂ) (fₙ : ℕ → ℝ → ℂ) (G ψ : ℝ → ℂ)
    (hfₙ : ∀ n, Integrable (fₙ n))
    (M : ℝ) (hM : ∀ n t, ‖fₙ n t‖ ≤ M)
    (hlim : ∀ t, Tendsto (fun n => fₙ n t) atTop (𝓝 (f t)))
    (hFourier : ∀ ξ, Tendsto (fun n => 𝓕 (fₙ n) ξ) atTop (𝓝 (G ξ)))
    (B : ℝ) (hB : ∀ n ξ, ψ ξ ≠ 0 → ‖𝓕 (fₙ n) ξ‖ ≤ B)
    (hψ : Integrable ψ) (hK : Integrable (𝓕 ψ)) (x : ℝ) :
    (∫ t, f t * 𝓕 ψ (t-x)) = 𝓕⁻ (fun ξ => G ξ*ψ ξ) x := by
  have hphys : Tendsto (fun n => ∫ t, fₙ n t * 𝓕 ψ (t-x)) atTop
      (𝓝 (∫ t, f t * 𝓕 ψ (t-x))) := by
    apply tendsto_integral_of_dominated_convergence (fun t => M*‖𝓕 ψ (t-x)‖)
    · intro n
      exact (hfₙ n).1.mul (hK.comp_sub_right x).1
    · exact (hK.comp_sub_right x).norm.const_mul M
    · intro n
      exact Eventually.of_forall (fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM n t) (norm_nonneg _))
    · exact Eventually.of_forall (fun t => (hlim t).mul_const _)
  have hfreq : Tendsto (fun n => ∫ ξ, 𝓕 (fₙ n) ξ * modulate x ψ ξ) atTop
      (𝓝 (∫ ξ, G ξ * modulate x ψ ξ)) := by
    apply tendsto_integral_of_dominated_convergence (fun ξ => B*‖ψ ξ‖)
    · intro n
      exact (fourier_continuous (hfₙ n)).aestronglyMeasurable.mul (integrable_modulate hψ x).1
    · exact hψ.norm.const_mul B
    · intro n
      apply Eventually.of_forall
      intro ξ
      by_cases hz : ψ ξ = 0
      · simp [modulate,hz]
      · rw [norm_mul,norm_modulate]
        exact mul_le_mul_of_nonneg_right (hB n ξ hz) (norm_nonneg _)
    · exact Eventually.of_forall (fun ξ => (hFourier ξ).mul_const _)
  have hid (n : ℕ) : (∫ ξ, 𝓕 (fₙ n) ξ*modulate x ψ ξ) =
      ∫ t, fₙ n t*𝓕 ψ (t-x) := by
    rw [integral_fourier_mul (hfₙ n) (integrable_modulate hψ x)]
    simp_rw [fourier_modulate]
  simp_rw [hid] at hfreq
  rw [fourierInv_eq_integral_modulate]
  exact tendsto_nhds_unique hphys hfreq

/-- Decay of the kernel pairing obtained from an actual integrable boundary
product. Both integrability conclusions are included to make clear that
Riemann--Lebesgue is not being applied to a totalized divergent integral. -/
theorem boundary_convolution_decay
    (f : ℝ → ℂ) (fₙ : ℕ → ℝ → ℂ) (G ψ : ℝ → ℂ)
    (hfₙ : ∀ n, Integrable (fₙ n))
    (M : ℝ) (hM : ∀ n t, ‖fₙ n t‖ ≤ M)
    (hlim : ∀ t, Tendsto (fun n => fₙ n t) atTop (𝓝 (f t)))
    (hFourier : ∀ ξ, Tendsto (fun n => 𝓕 (fₙ n) ξ) atTop (𝓝 (G ξ)))
    (B : ℝ) (hB : ∀ n ξ, ψ ξ ≠ 0 → ‖𝓕 (fₙ n) ξ‖ ≤ B)
    (hψ : Integrable ψ) (hK : Integrable (𝓕 ψ)) :
    Integrable (fun ξ => G ξ*ψ ξ) ∧
    (∀ x, Integrable (fun t => f t*𝓕 ψ (t-x))) ∧
    Tendsto (fun x : ℝ => ∫ t, f t*𝓕 ψ (t-x)) atTop (𝓝 0) := by
  refine ⟨integrable_frequency_pairing fₙ G ψ hfₙ hFourier B hB hψ,
    integrable_physical_pairing f fₙ ψ hfₙ M hM hlim hK, ?_⟩
  simp_rw [boundary_pairing f fₙ G ψ hfₙ M hM hlim hFourier B hB hψ hK,
    Real.fourierInv_eq_fourier_comp_neg]
  exact (Real.zero_at_infty_fourier _).mono_left atTop_le_cocompact

#print axioms boundary_convolution_decay

end Erdos371.FourierBoundary
