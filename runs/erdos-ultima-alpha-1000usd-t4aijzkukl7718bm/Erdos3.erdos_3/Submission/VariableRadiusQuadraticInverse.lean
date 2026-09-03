import Submission.VariableRadiusQuadraticCorrelation
import Submission.NormalizedQuadraticInverse
import Submission.RelativeStableBohr

/-! The normalized U³ inverse with a freely selected averaging radius. -/
namespace Erdos3VariableRadiusQuadraticInverse
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr
  Erdos3LocalQuadraticInverse Erdos3DoubledBohrLocalization
  Erdos3UnlocalizedBilinearExtraction Erdos3CompatibleQuadraticCorrelation
  Erdos3UniformLocalQuadraticInverse Erdos3CorrelationSifting
  Erdos3ReducedLossQuadraticInverse Erdos3PolynomialRankSkewSymmetry
  Erdos3AveragedAntisymmetry Erdos3LocalPhaseDuality Erdos3BiasedSkewDifferences
  Erdos3CrossSpectralSymmetry Erdos3VariableRadiusQuadraticCorrelation
  Erdos3NormalizedQuadraticInverse Erdos3RelativeStableBohr
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- One character set works for every positive radius at most 1/16. The
phase may depend on the selected radius but remains quadratic on the fixed
outer domain. The normalized correlation lower bound is radius-independent. -/
theorem variable_radius_local_quadratic_inverse (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), C.card ≤ normalizedRank δ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/16 → ∃ q : G → G → ℂ, (∀ a x, ‖q a x‖ = 1) ∧
      (∀ a, IsLocallyQuadratic (bohr C (1/16) : Set G) (q a)) ∧
      normalizedCorrelation δ ≤
        𝔼 a, ‖𝔼 y : bohr C ρ, f (a+y)*conj (q a y)‖^2 := by
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
  let C := E.image (fun χ ↦ χ.compAddMonoidHom (Erdos3LocalQuadraticIntegration.halfHom h2))
  refine ⟨C,card_image_le.trans hE,?_⟩
  intro ρ hρ hρmax
  obtain ⟨q,hq,hquad,hcorr⟩ := variable_radius_compatible_quadratic_correlation h2 f hf T hT F a₀ χ₀ E hF hdiff hEP hρ hρmax
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
  exact ⟨q,hq,hquad,hc⟩

/-- A stable radius can be selected after the character set is known.
Quadraticity is retained on a larger fixed Bohr domain, leaving room for
small translations. -/
theorem stable_radius_local_quadratic_inverse
    (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) {z : ℕ} (hz : 0 < z) :
    ∃ C : Finset (AddChar G ℂ), ∃ ρ : ℝ, ∃ q : G → G → ℂ,
      C.card ≤ normalizedRank δ ∧ 1/64 ≤ ρ ∧ ρ ≤ 1/32 ∧
      RelativeStable C z ρ ∧ (∀ a x, ‖q a x‖ = 1) ∧
      (∀ a, IsLocallyQuadratic (bohr C (1/16) : Set G) (q a)) ∧
      normalizedCorrelation δ ≤ 𝔼 a, ‖𝔼 y : bohr C ρ, f (a+y)*conj (q a y)‖^2 := by
  obtain ⟨C,hC,hinv⟩ := variable_radius_local_quadratic_inverse h2 f hf hδ hU
  obtain ⟨ρ,hρ,hρmax,hstable⟩ := exists_relative_stable C (by norm_num : (0 : ℝ) < 1/64) hz
  obtain ⟨q,hq,hquad,hcorr⟩ := hinv ρ (by linarith) (by linarith)
  exact ⟨C,ρ,q,hC,hρ,by linarith,hstable,hq,hquad,hcorr⟩

#print axioms variable_radius_local_quadratic_inverse
#print axioms stable_radius_local_quadratic_inverse
end Erdos3VariableRadiusQuadraticInverse
