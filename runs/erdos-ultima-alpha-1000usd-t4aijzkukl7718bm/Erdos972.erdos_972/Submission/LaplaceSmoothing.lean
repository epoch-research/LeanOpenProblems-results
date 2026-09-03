import FormalConjecturesUtil

/-! Fourier smoothing of a bounded function from continuous boundary values of its
Abel-regularized Fourier transform. This is an auxiliary analytic result, not the
prime-pair conjecture. -/
namespace Erdos972LaplaceSmoothing

open MeasureTheory Filter Set
open scoped Topology FourierTransform SchwartzMap

noncomputable def phase (x t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t * x : ℝ) * Complex.I)

lemma phase_norm (x t : ℝ) : ‖phase x t‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma continuous_phase (x : ℝ) : Continuous (phase x) := by
  unfold phase
  fun_prop

lemma fourier_modulation (φ : ℝ → ℂ) (x t : ℝ) :
    𝓕 (fun ξ => phase x ξ * φ ξ) t = 𝓕 φ (t - x) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [phase, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma integral_fourier_mul_swap {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, 𝓕 f ξ * g ξ) = ∫ t, f t * 𝓕 g t := by
  simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg

lemma integrable_modulation {φ : ℝ → ℂ} (hφ : Integrable φ) (x : ℝ) :
    Integrable (fun ξ => phase x ξ * φ ξ) := by
  apply hφ.norm.mono' ((continuous_phase x).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  filter_upwards with ξ
  simp only [Pi.mul_apply, norm_mul, phase_norm, one_mul, le_refl]

/-- An exact boundary Fourier identity. The approximating functions are uniformly
bounded, whereas their Fourier transforms need only be bounded on the support of
the test function. -/
theorem boundary_pairing {g : ℝ → ℂ} {gₙ : ℕ → ℝ → ℂ} {B : ℝ → ℂ}
    (hgₙ : ∀ n, Integrable (gₙ n))
    (hlim : ∀ᵐ t, Tendsto (fun n => gₙ n t) atTop (𝓝 (g t)))
    (C : ℝ) (hbound : ∀ n t, ‖gₙ n t‖ ≤ C)
    (hFourier : ∀ ξ, Tendsto (fun n => 𝓕 (gₙ n) ξ) atTop (𝓝 (B ξ)))
    (φ : 𝓢(ℝ, ℂ)) (D : ℝ)
    (hD : ∀ n ξ, φ ξ ≠ 0 → ‖𝓕 (gₙ n) ξ‖ ≤ D) (x : ℝ) :
    (∫ t, g t * 𝓕 φ (t - x)) = 𝓕 (fun ξ => B ξ * φ ξ) (-x) := by
  have hleft : Tendsto (fun n => ∫ t, gₙ n t * 𝓕 φ (t - x)) atTop
      (𝓝 (∫ t, g t * 𝓕 φ (t - x))) := by
    apply tendsto_integral_of_dominated_convergence (fun t => C * ‖𝓕 φ (t - x)‖)
    · intro n
      exact (hgₙ n).aestronglyMeasurable.mul
        ((𝓕 φ).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    · exact ((𝓕 φ).integrable.comp_sub_right x).norm.const_mul C
    · intro n
      filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound n t) (norm_nonneg _)
    · filter_upwards [hlim] with t ht
      exact ht.mul_const _
  have hright : Tendsto (fun n => ∫ ξ, 𝓕 (gₙ n) ξ * (phase x ξ * φ ξ)) atTop
      (𝓝 (∫ ξ, B ξ * (phase x ξ * φ ξ))) := by
    apply tendsto_integral_of_dominated_convergence (fun ξ => D * ‖φ ξ‖)
    · intro n
      exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        continuous_inner (hgₙ n)).aestronglyMeasurable.mul
        ((continuous_phase x).mul φ.continuous).aestronglyMeasurable
    · exact φ.integrable.norm.const_mul D
    · intro n
      filter_upwards with ξ
      by_cases hξ : φ ξ = 0
      · simp [hξ]
      · simp only [norm_mul, phase_norm, one_mul]
        exact mul_le_mul_of_nonneg_right (hD n ξ hξ) (norm_nonneg _)
    · filter_upwards with ξ
      exact (hFourier ξ).mul_const _
  have heq (n : ℕ) : (∫ t, gₙ n t * 𝓕 φ (t - x)) =
      ∫ ξ, 𝓕 (gₙ n) ξ * (phase x ξ * φ ξ) := by
    rw [integral_fourier_mul_swap (hgₙ n) (integrable_modulation φ.integrable x)]
    simp only [fourier_modulation, SchwartzMap.fourier_coe]
  have hid := tendsto_nhds_unique hleft (hright.congr (fun n => (heq n).symm))
  rw [hid, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [phase, smul_eq_mul]
  have hp : (-2 * Real.pi * ξ * -x : ℝ) = 2 * Real.pi * ξ * x := by ring
  rw [hp]
  ring

/-- A continuous boundary transform makes every band-limited Schwartz smoothing
of the bounded original function tend to zero at infinity. -/
theorem boundary_smoothing_tendsto {g : ℝ → ℂ} {gₙ : ℕ → ℝ → ℂ} {B : ℝ → ℂ}
    (hgₙ : ∀ n, Integrable (gₙ n))
    (hlim : ∀ᵐ t, Tendsto (fun n => gₙ n t) atTop (𝓝 (g t)))
    (C : ℝ) (hbound : ∀ n t, ‖gₙ n t‖ ≤ C)
    (hFourier : ∀ ξ, Tendsto (fun n => 𝓕 (gₙ n) ξ) atTop (𝓝 (B ξ)))
    (φ : 𝓢(ℝ, ℂ)) (D : ℝ)
    (hD : ∀ n ξ, φ ξ ≠ 0 → ‖𝓕 (gₙ n) ξ‖ ≤ D) :
    Tendsto (fun x => ∫ t, g t * 𝓕 φ (t - x)) atTop (𝓝 0) := by
  simp_rw [boundary_pairing hgₙ hlim C hbound hFourier φ D hD]
  exact (Real.zero_at_infty_fourier _).comp
    (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)

noncomputable def damped (g : ℝ → ℂ) (ε : ℝ) : ℝ → ℂ :=
  (Ioi 0).indicator (fun t => Complex.exp (-(ε : ℂ) * t) * g t)

lemma integrable_damped {g : ℝ → ℂ} (hg : AEStronglyMeasurable g)
    (C : ℝ) (hC : ∀ t, ‖g t‖ ≤ C) {ε : ℝ} (hε : 0 < ε) :
    Integrable (damped g ε) := by
  have he : IntegrableOn (fun t : ℝ => C * Real.exp (-ε * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hε) 0).const_mul C
  apply ((integrable_indicator_iff measurableSet_Ioi).mpr he).mono'
    (((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(ε : ℂ) * t))).aestronglyMeasurable.mul hg).indicator measurableSet_Ioi)
  filter_upwards with t
  by_cases ht : 0 < t
  · simp only [damped, Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), Pi.mul_apply, norm_mul, Complex.norm_exp,
      Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (hC t) (Real.exp_pos _).le |>.trans_eq (mul_comm _ _)
  · simp [damped, ht]

lemma norm_damped_le {g : ℝ → ℂ} (C : ℝ) (hC : ∀ t, ‖g t‖ ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : ‖damped g ε t‖ ≤ C := by
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  by_cases ht : 0 < t
  · simp only [damped, Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), Pi.mul_apply, norm_mul, Complex.norm_exp,
      Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    calc
      _ ≤ 1 * C := mul_le_mul (Real.exp_le_one_iff.mpr (by nlinarith))
        (hC t) (norm_nonneg _) zero_le_one
      _ = C := one_mul _
  · simpa [damped, ht] using hC0

noncomputable def dampingParameter (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma dampingParameter_pos (n : ℕ) : 0 < dampingParameter n := by
  unfold dampingParameter
  positivity

lemma dampingParameter_le_one (n : ℕ) : dampingParameter n ≤ 1 := by
  unfold dampingParameter
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma dampingParameter_tendsto : Tendsto dampingParameter atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma damped_tendsto {g : ℝ → ℂ} (hzero : ∀ t ≤ 0, g t = 0) (t : ℝ) :
    Tendsto (fun n => damped g (dampingParameter n) t) atTop (𝓝 (g t)) := by
  by_cases ht : 0 < t
  · simp only [damped, Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have hz : Tendsto (fun n => -(dampingParameter n : ℂ) * t) atTop (𝓝 0) := by
      simpa using ((Complex.continuous_ofReal.tendsto 0).comp dampingParameter_tendsto |>.neg.mul_const (t : ℂ))
    simpa using ((Complex.continuous_exp.tendsto 0).comp hz).mul_const (g t)
  · simp [damped, ht, hzero t (le_of_not_gt ht)]

lemma fourier_damped (g : ℝ → ℂ) (ε ξ : ℝ) :
    𝓕 (damped g ε) ξ = ∫ t in Ioi (0 : ℝ),
      Complex.exp (-((ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I) * t) * g t := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : 0 < t
  · simp only [damped, Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp [damped, ht]

/-- A bounded Laplace-Tauberian smoothing theorem. Continuous extension of the
Laplace transform to the imaginary axis implies decay of every compact-frequency
Schwartz average. -/
theorem laplace_smoothing_tendsto {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g) (hzero : ∀ t ≤ 0, g t = 0)
    (C : ℝ) (hC : ∀ t, ‖g t‖ ≤ C)
    (F : ℝ × ℝ → ℂ)
    (hF : ContinuousOn F {z | 0 ≤ z.1 ∧ z.1 ≤ 1})
    (hLap : ∀ ε ξ : ℝ, 0 < ε → ε ≤ 1 →
      (∫ t in Ioi (0 : ℝ),
        Complex.exp (-((ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I) * t) * g t) = F (ε, ξ))
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    Tendsto (fun x => ∫ t, g t * 𝓕 φ (t - x)) atTop (𝓝 0) := by
  have hFT (n : ℕ) (ξ : ℝ) :
      𝓕 (damped g (dampingParameter n)) ξ = F (dampingParameter n, ξ) := by
    rw [fourier_damped, hLap _ _ (dampingParameter_pos n) (dampingParameter_le_one n)]
  have hflim (ξ : ℝ) : Tendsto
      (fun n => 𝓕 (damped g (dampingParameter n)) ξ) atTop (𝓝 (F (0, ξ))) := by
    simp_rw [hFT]
    apply (hF (0, ξ) ⟨le_rfl, zero_le_one⟩).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨dampingParameter_tendsto.prodMk_nhds tendsto_const_nhds, ?_⟩
    exact Eventually.of_forall fun n => ⟨(dampingParameter_pos n).le, dampingParameter_le_one n⟩
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ tsupport (φ : ℝ → ℂ)
  have hK : IsCompact K := isCompact_Icc.prod hφ
  have hc : ContinuousOn (fun z => ‖F z‖) K :=
    hF.norm.mono (fun _ hz => hz.1)
  obtain ⟨D, hD⟩ := bddAbove_def.mp (hK.bddAbove_image hc)
  apply boundary_smoothing_tendsto
    (fun n => integrable_damped hg C hC (dampingParameter_pos n))
    (ae_of_all _ (damped_tendsto hzero)) C
    (fun n t => norm_damped_le C hC (dampingParameter_pos n).le t) hflim φ D
  intro n ξ hξ
  rw [hFT]
  exact hD _ (by exact ⟨(dampingParameter n, ξ),
    ⟨⟨(dampingParameter_pos n).le, dampingParameter_le_one n⟩,
      subset_tsupport _ (Function.mem_support.mpr hξ)⟩, rfl⟩)

#print axioms laplace_smoothing_tendsto

end Erdos972LaplaceSmoothing
