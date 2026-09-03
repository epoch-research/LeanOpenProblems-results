import Submission.NormalizedCompatibleQuadraticCorrelation
import Submission.ReducedLossQuadraticInverse

/-! A normalized local U³ inverse with polynomial rank and polynomial
correlation. The direction fiber retains polynomial density. -/
namespace Erdos3NormalizedQuadraticInverse
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr
  Erdos3LocalQuadraticInverse Erdos3DoubledBohrLocalization
  Erdos3UnlocalizedBilinearExtraction Erdos3CompatibleQuadraticCorrelation
  Erdos3UniformLocalQuadraticInverse Erdos3CorrelationSifting
  Erdos3ReducedLossQuadraticInverse Erdos3PolynomialRankSkewSymmetry
  Erdos3AveragedAntisymmetry Erdos3LocalPhaseDuality Erdos3BiasedSkewDifferences
  Erdos3CrossSpectralSymmetry Erdos3NormalizedCompatibleQuadraticCorrelation
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def normalizedRank (δ : ℝ) : ℕ :=
  fixedRadiusRank (retainedDensity δ) ((δ/2)^8*(retainedDensity δ)^4) (δ/8)
noncomputable def normalizedCorrelation (δ : ℝ) : ℝ := δ^9*(retainedDensity δ)^5/4096

lemma normalizedCorrelation_pos {δ : ℝ} (hδ : 0 < δ) : 0 < normalizedCorrelation δ := by
  have hβ := retainedDensity_pos hδ
  unfold normalizedCorrelation
  positivity

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Averaged NORMALIZED local quadratic correlation. Both the inverse correlation
and the Bohr rank have polynomial bounds in the inverse U³ parameter. -/
theorem normalized_local_quadratic_inverse (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → G → ℂ,
      C.card ≤ normalizedRank δ ∧ (∀ a x, ‖q a x‖ = 1) ∧
      (∀ a, IsLocallyQuadratic (bohr C (1/16) : Set G) (q a)) ∧
      normalizedCorrelation δ ≤
        𝔼 a, ‖𝔼 y : bohr C (1/16), f (a+y)*conj (q a y)‖^2 := by
  have hδ1 : δ ≤ 1 := hU.trans (uniformityPower_le_one 2 f hf)
  obtain ⟨T,F,a₀,χ₀,hT0,hsize,hF0,hF,hdiff,hcoef⟩ :=
    large_U3_unlocalized_bilinear f hf hδ hU
  have hT : T.Nonempty := ⟨0,hT0⟩
  have hσ : 0 < density T := density_pos T hT
  have hβ := retainedDensity_pos hδ
  have hβσ := retainedDensity_le_support T hδ hsize
  have hmean : (δ/2)^8*(density T)^4 ≤ pairSkewBias T F := by
    have hh := large_coefficients_average_bias_lower T hT
      (fun x ↦ f (x+a₀)) (fun x ↦ f x*χ₀ x) F
      (fun x ↦ hf _) (fun x ↦ by simpa only [norm_mul,AddChar.norm_apply,mul_one] using hf x)
      hdiff (show 0 ≤ δ/2 by positivity)
      (fun t ht ↦ by rw [shifted_mixed_coefficient]; exact hcoef t ht)
    change (δ/2)^8*(density T)^7 ≤ averageSkewBias T F at hh
    rw [averageSkewBias_eq_normalized T hT F] at hh
    apply (mul_le_mul_iff_right₀ (pow_pos hσ 3)).mp
    calc
      _ = (δ/2)^8*(density T)^7 := by ring
      _ ≤ _ := hh
      _ = _ := by ring
  have hΛ : (δ/2)^8*(retainedDensity δ)^4 ≤ pairSkewBias T F :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ.le hβσ 4) (by positivity)).trans hmean
  have hΛ1 : (δ/2)^8*(retainedDensity δ)^4 ≤ 1 := by
    apply hΛ.trans
    letI : Nonempty T := hT.to_subtype
    apply expect_le univ_nonempty
    intro s _
    exact expect_le univ_nonempty (fun t _ ↦ normalizedSkewBias_le_one T F ((s : G)-t))
  obtain ⟨E,hE,hEP,hsym⟩ := fixed_radius_cross_symmetry T hT0 F hF hdiff hβ hβσ
    (by positivity : 0 < (δ/2)^8*(retainedDensity δ)^4) hΛ1
    (by positivity : 0 < δ/8) (by linarith : δ/8 ≤ 1)
  obtain ⟨q,hq,hquad,hcorr⟩ := normalized_compatible_quadratic_correlation h2 f hf T hT F a₀ χ₀ E hF hdiff hEP
    (by positivity : 0 < δ/2) (by linarith : δ/2 ≤ 1)
    (by positivity : 0 < (δ/2)^8*(retainedDensity δ)^4) hΛ hcoef
    (by simpa only [show δ/2/4 = δ/8 by ring] using hsym)
  have hl : normalizedCorrelation δ ≤ (δ/2)*((δ/2)^8*(retainedDensity δ)^4)*density T/8 := by
    calc
      _ = (δ/2)*((δ/2)^8*(retainedDensity δ)^4)*retainedDensity δ/8 := by
        unfold normalizedCorrelation
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hβσ (by positivity)) (by norm_num)
  have hc := hl.trans hcorr
  rw [doubledBohr_eq_bohr_pullback h2] at hquad hc
  exact ⟨_,q,card_image_le.trans hE,hq,hquad,hc⟩

#print axioms normalized_local_quadratic_inverse
end Erdos3NormalizedQuadraticInverse
