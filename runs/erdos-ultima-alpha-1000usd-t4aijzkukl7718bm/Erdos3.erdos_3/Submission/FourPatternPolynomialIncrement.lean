import Submission.NormalizedQuadraticDensityIncrement

/-! Four-pattern-free sets have a polynomial relative density increment on a
local quadratic phase cell. Relative iteration remains a separate problem. -/
namespace Erdos3FourPatternPolynomialIncrement
open Erdos3NormalizedQuadraticDensityIncrement Erdos3NormalizedQuadraticInverse
  Erdos3NormalizedQuadraticPowerBounds Erdos3SingleExponentialQuadraticInverse
  Erdos3InteriorQuadraticDensityIncrement Erdos3FourPatternQuadraticStructure
  Erdos3UniformityCounting Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3FiniteBohr Erdos3LocalQuadraticInverse Erdos3CorrelationSifting Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def fourPolynomialDenominator : ℝ := correlationDenominator*(8 : ℝ)^15908272
noncomputable def fourPolynomialGain (α : ℝ) : ℝ := α^63633088/fourPolynomialDenominator

lemma fourPolynomialDenominator_pos : 0 < fourPolynomialDenominator :=
  mul_pos correlationDenominator_pos (pow_pos (by norm_num) _)

lemma fourPolynomialGain_pos {α : ℝ} (hα : 0 < α) : 0 < fourPolynomialGain α :=
  div_pos (pow_pos hα _) fourPolynomialDenominator_pos

lemma threshold_correlation_power (α : ℝ) :
    (((α^4/8)^8)^1988534)/correlationDenominator = fourPolynomialGain α := by
  unfold fourPolynomialGain fourPolynomialDenominator
  simp only [div_pow,← pow_mul,div_div]
  change α^63633088/((8 : ℝ)^15908272*correlationDenominator) =
    α^63633088/(correlationDenominator*(8 : ℝ)^15908272)
  rw [mul_comm]

variable {F : Type*} [Field F] [Fintype F]

/-- A positive increment whose gain and relative cell-size bounds are fixed
powers of density, rather than exponentials of inverse density. -/
theorem four_pattern_free_polynomial_density_increment
    (h2 : Function.Bijective (fun x : F ↦ x+x))
    (v : Fin 4 → F) (hv : Function.Injective v) (A : Finset F) (hA : A.Nonempty)
    (hsize : 4 ≤ (density A)^3*(Fintype.card F : ℝ))
    (hdiag : ∀ x d : F, (∀ i : Fin 4, x+v i*d ∈ A) → d = 0) :
    ∃ C : Finset (AddChar F ℂ), ∃ q : F → ℂ, ∃ a : F, ∃ S : Finset F,
      (C.card : ℝ) ≤ fourRankConstant*(1/density A)^1069036416 ∧
      (∀ x, ‖q x‖ = 1) ∧ IsLocallyQuadratic (bohr C (1/16) : Set F) q ∧
      IsInteriorPhaseCell (phaseResolution (fourPolynomialGain (density A))) (bohr C (1/16)) q S ∧
      S.Nonempty ∧ (fourPolynomialGain (density A))^3/2048*((bohr C (1/16)).card : ℝ) ≤ (S.card : ℝ) ∧
      density A+fourPolynomialGain (density A)/16 ≤
        ((S.filter (fun x ↦ a+x ∈ A)).card : ℝ)/(S.card : ℝ) := by
  have hα := density_pos A hA
  have hU := pattern_free_uniformity_lower 2 v hv A hA hsize hdiag
  have hU' : ((density A)^4/8)^8 ≤
      uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)) := by
    simpa only [show 2+2 = 4 from rfl,show 2^(2+1) = 8 from rfl,
      show (2 : ℝ)*(4 : ℕ) = 8 by norm_num] using hU.le
  have hδ : 0 < ((density A)^4/8)^8 := by positivity
  have hδ1 : ((density A)^4/8)^8 ≤ 1 := hU'.trans
    (uniformityPower_le_one 2 _ (fun x ↦ by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using centered_indicator_bound A x))
  have hcorr : fourPolynomialGain (density A) ≤ normalizedCorrelation (((density A)^4/8)^8) := by
    rw [← threshold_correlation_power]
    exact normalizedCorrelation_power_lower hδ hδ1
  obtain ⟨C,q,a,S,hC,hq,hquad,hcell,hS,hcard,hinc⟩ := normalized_quadratic_density_increment h2 A
    hδ hU' (fourPolynomialGain_pos hα) hcorr
  have hrank := normalizedRank_power_bound hδ hδ1
  rw [threshold_power] at hrank
  have hC' : (C.card : ℝ) ≤ normalizedRank (((density A)^4/8)^8) := by exact_mod_cast hC
  refine ⟨C,q,a,S,?_,hq,hquad,hcell,hS,hcard,hinc⟩
  simpa only [fourRankConstant,mul_assoc] using hC'.trans hrank

#print axioms four_pattern_free_polynomial_density_increment
end Erdos3FourPatternPolynomialIncrement
