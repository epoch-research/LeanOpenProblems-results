import Submission.AntidiagonalTwistedEnergy

/-! A masked averaged antisymmetry estimate, obtained from the exact
antidiagonal twisted-energy identity. No pointwise symmetry is assumed. -/
namespace Erdos3AveragedAntisymmetry
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3SpectralGraphEnergy
  Erdos3LinearFormsUniformity Erdos3TwistedCorrelationEnergy
  Erdos3AntidiagonalTwistedEnergy Erdos3LocalPhaseDuality
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def localSkewBias (T : Finset G) (F : G → AddChar G ℂ) (d : G) : ℂ :=
  𝔼 x, if x ∈ T then skewPhase F x d else 0

noncomputable def averageSkewBias (T : Finset G) (F : G → AddChar G ℂ) : ℝ :=
  𝔼 u, 𝔼 v, if u ∈ T ∧ v ∈ T then ‖localSkewBias T F (u-v)‖ else 0

noncomputable def maskedSkewRow (T : Finset G) (w : G → ℂ)
    (F : G → AddChar G ℂ) (x : G) : ℂ :=
  if x ∈ T then 𝔼 u, conj (w u)*skewPhase F x u else 0

lemma complex_expect_cauchy_schwarz {I : Type*} [Fintype I] (f g : I → ℂ) :
    ‖𝔼 x, f x*g x‖^2 ≤ (𝔼 x, ‖f x‖^2)*(𝔼 x, ‖g x‖^2) := by
  have hn : ‖𝔼 x, f x*g x‖ ≤ 𝔼 x, ‖f x‖*‖g x‖ := by
    simpa only [norm_mul] using (RCLike.norm_expect_le (K := ℂ) (f := fun x ↦ f x*g x))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (expect_mul_sq_le_sq_mul_sq univ (fun x ↦ ‖f x‖) (fun x ↦ ‖g x‖))

lemma support_mass_le (T : Finset G) (w : G → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (hs : ∀ x, x ∉ T → w x = 0) :
    (𝔼 x, ‖w x‖^2) ≤ (T.card : ℝ)/(Fintype.card G : ℝ) := by
  calc
    _ ≤ 𝔼 x : G, if x ∈ T then (1 : ℝ) else 0 := by
      apply expect_le_expect
      intro x _
      by_cases hx : x ∈ T
      · simp only [if_pos hx]
        nlinarith [hw x,norm_nonneg (w x)]
      · simp only [if_neg hx,hs x hx,norm_zero,zero_pow (by decide : 2 ≠ 0),le_refl]
    _ = _ := by simp [Fintype.expect_eq_sum_div_card]

lemma skewForm_eq_masked_row (T : Finset G) (w : G → ℂ) (F : G → AddChar G ℂ)
    (hs : ∀ x, x ∉ T → w x = 0) :
    skewForm w F = 𝔼 x, w x*maskedSkewRow T w F x := by
  unfold skewForm
  apply expect_congr rfl
  intro x _
  by_cases hx : x ∈ T
  · simp only [maskedSkewRow,if_pos hx,mul_assoc,mul_expect]
  · simp only [maskedSkewRow,if_neg hx,hs x hx,zero_mul]
    simp

lemma masked_row_square (T : Finset G) (w : G → ℂ) (F : G → AddChar G ℂ)
    (hs : ∀ x, x ∉ T → w x = 0)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v) (x : G) :
    ((‖maskedSkewRow T w F x‖^2 : ℝ) : ℂ) =
      𝔼 u, 𝔼 v, conj (w u)*w v*(if x ∈ T then skewPhase F x (u-v) else 0) := by
  by_cases hx : x ∈ T
  · simp only [maskedSkewRow,if_pos hx,ofReal_norm_expect_sq,map_mul,starRingEnd_self_apply]
    apply expect_congr rfl
    intro u _
    apply expect_congr rfl
    intro v _
    by_cases hu : u ∈ T
    · by_cases hv : v ∈ T
      · rw [← skewPhase_sub_right T F hF x hu hv]
        ring
      · simp only [hs v hv,mul_zero,zero_mul]
    · simp only [hs u hu,map_zero,zero_mul]
  · simp only [maskedSkewRow,if_neg hx,norm_zero,zero_pow (by decide : 2 ≠ 0),
      Complex.ofReal_zero,mul_zero]
    simp

lemma masked_row_energy (T : Finset G) (w : G → ℂ) (F : G → AddChar G ℂ)
    (hs : ∀ x, x ∉ T → w x = 0)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v) :
    ((𝔼 x, ‖maskedSkewRow T w F x‖^2 : ℝ) : ℂ) =
      𝔼 u, 𝔼 v, conj (w u)*w v*localSkewBias T F (u-v) := by
  rw [ofReal_expect]
  simp_rw [masked_row_square T w F hs hF]
  calc
    _ = 𝔼 u, 𝔼 v, 𝔼 x, conj (w u)*w v*
        (if x ∈ T then skewPhase F x (u-v) else 0) := (expect_rotate_three _).symm
    _ = _ := by simp only [localSkewBias,mul_expect]

lemma masked_row_energy_le (T : Finset G) (w : G → ℂ) (F : G → AddChar G ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (hs : ∀ x, x ∉ T → w x = 0)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v) :
    (𝔼 x, ‖maskedSkewRow T w F x‖^2) ≤ averageSkewBias T F := by
  have he := congrArg Complex.re (masked_row_energy T w F hs hF)
  simp only [Complex.ofReal_re,expect_re] at he
  rw [he]
  apply expect_le_expect
  intro u _
  apply expect_le_expect
  intro v _
  by_cases hu : u ∈ T
  · by_cases hv : v ∈ T
    · simp only [hu,hv,and_self,if_true]
      apply (Complex.re_le_norm _).trans
      simp only [norm_mul,Complex.norm_conj]
      have hp : ‖w u‖*‖w v‖ ≤ 1 :=
        (mul_le_mul (hw u) (hw v) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _)
    · simp only [hv,and_false,if_false,hs v hv,mul_zero,zero_mul,Complex.zero_re,le_refl]
  · simp only [hu,false_and,if_false,hs u hu,map_zero,zero_mul,Complex.zero_re,le_refl]

lemma averageSkewBias_nonneg (T : Finset G) (F : G → AddChar G ℂ) :
    0 ≤ averageSkewBias T F :=
  expect_nonneg (fun _ _ ↦ expect_nonneg (fun _ _ ↦ by split_ifs <;> positivity))

/-- A masked quadratic form is controlled by the average bias of the
antisymmetric phases on differences of its support. -/
theorem skewForm_sq_le_average_bias (T : Finset G) (w : G → ℂ)
    (F : G → AddChar G ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hs : ∀ x, x ∉ T → w x = 0)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v) :
    ‖skewForm w F‖^2 ≤ ((T.card : ℝ)/(Fintype.card G : ℝ))*averageSkewBias T F := by
  rw [skewForm_eq_masked_row T w F hs]
  apply (complex_expect_cauchy_schwarz w (maskedSkewRow T w F)).trans
  exact mul_le_mul (support_mass_le T w hw hs) (masked_row_energy_le T w F hw hs hF)
    (expect_nonneg (fun _ _ ↦ sq_nonneg _)) (by positivity)

/-- The phase-retaining energy forces an averaged antisymmetry bias.
The bias is masked on T, so no arbitrary extension of F is used. -/
theorem twistedEnergy_sq_le_average_bias (T : Finset G) (b : G → ℂ)
    (F : G → AddChar G ℂ) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hs : ∀ x, x ∉ T → b x = 0)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v) :
    ‖twistedEnergy b F‖^2 ≤ ((T.card : ℝ)/(Fintype.card G : ℝ))*averageSkewBias T F := by
  rw [twistedEnergy_eq_skew_forms T b F hs hF]
  calc
    _ ≤ 𝔼 s, ‖skewForm (fiberWeight b F s) F‖^2 := by
      simpa only [one_mul] using mean_product_sq_le (fun _ : G ↦ (1 : ℂ))
        (fun s ↦ skewForm (fiberWeight b F s) F) (fun _ ↦ by simp)
    _ ≤ _ := expect_le univ_nonempty (fun s _ ↦
      skewForm_sq_le_average_bias T (fiberWeight b F s) F
        (fiberWeight_norm_le_one b F hb s) (fiberWeight_support T b F hs s) hF)

/-- The corresponding eighth-power bound for the original mixed correlation. -/
theorem mixed_correlation_eighth_le (T : Finset G) (b u v : G → ℂ)
    (F : G → AddChar G ℂ) (hb : ∀ x, ‖b x‖ ≤ 1)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (hs : ∀ x, x ∉ T → b x = 0)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v) :
    ‖𝔼 h, b h*mixedCoefficient u v F h‖^8 ≤
      ((T.card : ℝ)/(Fintype.card G : ℝ))*averageSkewBias T F := by
  have h1 := mixed_correlation_fourth_le T b u v F hu hv hs hF
  have h2 := twistedEnergy_sq_le_average_bias T b F hb hs hF
  rw [twistedEnergy_eq_derivative_fourier,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (expect_nonneg (fun _ _ ↦ sq_nonneg _))] at h2
  have h3 := pow_le_pow_left₀ (by positivity) h1 2
  rw [← pow_mul] at h3
  exact h3.trans h2

/-- Large compatible mixed coefficients imply a quantitative average bias,
without assuming that the antisymmetric pairing is pointwise small. -/
theorem large_coefficients_average_bias (T : Finset G) (u v : G → ℂ)
    (F : G → AddChar G ℂ) (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v)
    {κ : ℝ} (hκ : 0 ≤ κ) (hc : ∀ t ∈ T, κ ≤ ‖mixedCoefficient u v F t‖^2) :
    (κ*((T.card : ℝ)/(Fintype.card G : ℝ)))^8 ≤
      ((T.card : ℝ)/(Fintype.card G : ℝ))*averageSkewBias T F := by
  obtain ⟨b,hb,hs,he⟩ := aligned_phase_duality T u v F hu hv hF hκ hc
  have h2 := twistedEnergy_sq_le_average_bias T b F hb hs hF
  rw [twistedEnergy_eq_derivative_fourier,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (expect_nonneg (fun _ _ ↦ sq_nonneg _))] at h2
  have h3 := pow_le_pow_left₀ (by positivity) he 2
  rw [← pow_mul] at h3
  exact h3.trans h2

/-- Dividing out the positive support density gives an explicit lower bound. -/
theorem large_coefficients_average_bias_lower (T : Finset G) (hT : T.Nonempty)
    (u v : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (hF : ∀ u ∈ T, ∀ v ∈ T, F (u-v) = F u-F v)
    {κ : ℝ} (hκ : 0 ≤ κ) (hc : ∀ t ∈ T, κ ≤ ‖mixedCoefficient u v F t‖^2) :
    κ^8*((T.card : ℝ)/(Fintype.card G : ℝ))^7 ≤ averageSkewBias T F := by
  have hσ : 0 < (T.card : ℝ)/(Fintype.card G : ℝ) :=
    div_pos (by exact_mod_cast hT.card_pos) (by exact_mod_cast Fintype.card_pos)
  apply (mul_le_mul_iff_right₀ hσ).mp
  calc
    _ = (κ*((T.card : ℝ)/(Fintype.card G : ℝ)))^8 := by ring
    _ ≤ _ := large_coefficients_average_bias T u v F hu hv hF hκ hc
    _ = _ := by ring

open Erdos3FiniteBohr Erdos3LocalBilinearExtraction in
/-- The local frequency map extracted from large U³ has an unconditionally
proved averaged antisymmetry bias, with all localization offsets retained. -/
theorem large_U3_average_antisymmetry (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ D : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
    ∃ T : Finset G, ∃ a₀ : G, ∃ χ₀ : AddChar G ℂ,
      0 ∈ T ∧ T ⊆ bohr D (1/2) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        extractionLoss δ*(17 : ℝ)^(2*D.card)*(T.card : ℝ) ∧
      (D.card : ℝ) ≤ rankBound δ ∧ F 0 = 0 ∧
      (∀ x ∈ bohr D (1/2), ∀ y ∈ bohr D (1/2),
        x+y ∈ bohr D (1/2) → F (x+y) = F x+F y) ∧
      (∀ h ∈ T, ∀ k ∈ T, F (h-k) = F h-F k) ∧
      (∀ t ∈ T, δ/2 ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2) ∧
      (δ/2)^8*((T.card : ℝ)/(Fintype.card G : ℝ))^7 ≤ averageSkewBias T F := by
  obtain ⟨D,F,T,a₀,χ₀,h0,hsub,hsize,hrank,hF0,hadd,hdiff,hcoef⟩ :=
    large_U3_compatible_bilinear f hf hδ hU
  refine ⟨D,F,T,a₀,χ₀,h0,hsub,hsize,hrank,hF0,hadd,hdiff,hcoef,?_⟩
  apply large_coefficients_average_bias_lower T ⟨0,h0⟩
    (fun x ↦ f (x+a₀)) (fun x ↦ f x*χ₀ x) F
    (fun x ↦ hf _) (fun x ↦ by simpa only [norm_mul,AddChar.norm_apply,mul_one] using hf x)
    hdiff (by positivity)
  intro t ht
  rw [shifted_mixed_coefficient]
  exact hcoef t ht

#print axioms twistedEnergy_sq_le_average_bias
#print axioms large_coefficients_average_bias
#print axioms large_U3_average_antisymmetry
end Erdos3AveragedAntisymmetry
