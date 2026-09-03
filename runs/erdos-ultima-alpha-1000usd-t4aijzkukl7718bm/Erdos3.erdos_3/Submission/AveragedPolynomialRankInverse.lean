import Submission.PolynomialRankQuadraticInverse
import Submission.AveragedCompatibleQuadraticCorrelation

/-! A uniform local U³ inverse using the common spectral symmetry domain.
Its explicit rank formula avoids exponential losses in inverse density. -/
namespace Erdos3AveragedPolynomialRankInverse
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr
  Erdos3LocalQuadraticInverse Erdos3DoubledBohrLocalization
  Erdos3UnlocalizedBilinearExtraction Erdos3CompatibleQuadraticCorrelation
  Erdos3UniformLocalQuadraticInverse Erdos3CorrelationSifting
  Erdos3ReducedLossQuadraticInverse Erdos3PolynomialRankSkewSymmetry
  Erdos3AveragedAntisymmetry Erdos3LocalPhaseDuality Erdos3BiasedSkewDifferences
  Erdos3PolynomialRankQuadraticInverse Erdos3AveragedCompatibleQuadraticCorrelation
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Actual local quadratic correlation, with ambient-size-independent parameters
and a rank formula containing no exponentiation by inverse parameters. -/
theorem averaged_polynomial_rank_quadratic_inverse (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → G → ℂ,
      C.card ≤ sharpRank δ ∧ (∀ a x, ‖q a x‖ = 1) ∧
      (∀ a, IsLocallyQuadratic (bohr C (1/8) : Set G) (q a)) ∧
      sharpCorrelation δ ≤
        𝔼 a, ‖𝔼 y, if y ∈ bohr C (1/8) then f (a+y)*conj (q a y) else 0‖^2 := by
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
  obtain ⟨E,hE,hEP,hadd,hsym⟩ := fixed_radius_spectral_symmetry T hT0 F hF hdiff hβ hβσ
    (by positivity : 0 < (δ/2)^8*(retainedDensity δ)^4) hΛ
    (by positivity : 0 < δ/16) (by linarith : δ/16 ≤ 1)
  have hEc : E.card ≤ sharpRank δ := hE
  obtain ⟨q,hq,hquad,hcorr⟩ := averaged_compatible_quadratic_correlation h2 f hf T hT F a₀ χ₀ E hadd hdiff
    (by positivity : 0 < δ/2) (by linarith : δ/2 ≤ 1) hcoef
    (by simpa only [show δ/2/8 = δ/16 by ring] using hsym)
  have hpow : 8*(8385 : ℝ)^(2*E.card) ≤ 8*(8385 : ℝ)^(2*sharpRank δ) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 hEc)
  have hl : sharpCorrelation δ ≤ (δ/2)*density T/(4*(8385 : ℝ)^(2*E.card)) := by
    calc
      _ ≤ δ*density T/(8*(8385 : ℝ)^(2*sharpRank δ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβσ hδ.le) (by positivity)
      _ ≤ δ*density T/(8*(8385 : ℝ)^(2*E.card)) :=
        div_le_div_of_nonneg_left (mul_nonneg hδ.le hσ.le) (by positivity) hpow
      _ = _ := by ring
  have hc := hl.trans hcorr
  rw [doubledBohr_eq_bohr_pullback h2] at hquad hc
  exact ⟨_,q,card_image_le.trans hEc,hq,hquad,hc⟩

#print axioms averaged_polynomial_rank_quadratic_inverse
end Erdos3AveragedPolynomialRankInverse
