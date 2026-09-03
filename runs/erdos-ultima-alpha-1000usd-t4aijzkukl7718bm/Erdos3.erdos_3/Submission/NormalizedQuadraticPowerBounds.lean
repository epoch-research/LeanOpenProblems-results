import Submission.NormalizedQuadraticInverse
import Submission.SingleExponentialQuadraticInverse

/-! Explicit polynomial bounds for both rank and normalized local correlation. -/
namespace Erdos3NormalizedQuadraticPowerBounds
open Erdos3NormalizedQuadraticInverse Erdos3SingleExponentialQuadraticInverse
  Erdos3ReducedLossQuadraticInverse Erdos3PolynomialRankSkewSymmetry
  Erdos3QuadraticRankPowerBound Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3FiniteBohr Erdos3LocalQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def correlationDenominator : ℝ := 4096*extractionConstant^5

lemma correlationDenominator_pos : 0 < correlationDenominator := by
  have hC := extractionConstant_ge_one
  unfold correlationDenominator
  positivity

lemma retainedDensity_power_lower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ^397705/extractionConstant ≤ retainedDensity δ := by
  have hα := retainedDensity_pos hδ
  have hh := one_div_le_one_div_of_le (one_div_pos.mpr hα) (retainedDensity_inv_bound hδ hδ1)
  have hid (c d : ℝ) : 1/(c*(1/d)^397705) = d^397705/c := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul,← inv_pow]
  rw [hid,one_div_one_div] at hh
  exact hh

lemma normalizedCorrelation_power_lower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ^1988534/correlationDenominator ≤ normalizedCorrelation δ := by
  have hC : 0 < extractionConstant := lt_of_lt_of_le (by norm_num) extractionConstant_ge_one
  have hα := retainedDensity_power_lower hδ hδ1
  calc
    _ = δ^9*(δ^397705/extractionConstant)^5/4096 := by unfold correlationDenominator; ring
    _ ≤ _ := by unfold normalizedCorrelation; gcongr

lemma normalizedRank_power_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (normalizedRank δ : ℝ) ≤ rankConstant*(1/δ)^33407388 := by
  obtain ⟨ht,hαt,hΛt,hτt⟩ := inverse_parameter_bounds hδ hδ1
  have hα := retainedDensity_pos hδ
  have hτ : 1/tolerance (retainedDensity δ) (δ/8) ≤
      parameterConstant*(1/δ)^1590828 := by
    apply le_trans _ hτt
    apply one_div_le_one_div_of_le (tolerance_pos hα (by positivity : 0 < δ/16))
    unfold tolerance
    nlinarith
  have hh := fixedRadiusRank_power_bound hα (retainedDensity_le_one hδ hδ1)
    (by positivity : 0 < (δ/2)^8*(retainedDensity δ)^4)
    (by positivity : 0 < δ/8) ht hαt hΛt hτ
  apply hh.trans_eq
  simp only [rankConstant,mul_pow]
  ring

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- An averaged normalized local U³ inverse with polynomial quantitative costs
on BOTH rank and inverse correlation. -/
theorem polynomial_normalized_local_quadratic_inverse
    (h2 : Function.Bijective (fun x : G ↦ x+x)) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → G → ℂ,
      (C.card : ℝ) ≤ rankConstant*(1/δ)^33407388 ∧ (∀ a x, ‖q a x‖ = 1) ∧
      (∀ a, IsLocallyQuadratic (bohr C (1/16) : Set G) (q a)) ∧
      δ^1988534/correlationDenominator ≤
        𝔼 a, ‖𝔼 y : bohr C (1/16), f (a+y)*conj (q a y)‖^2 := by
  have hδ1 := hU.trans (uniformityPower_le_one 2 f hf)
  obtain ⟨C,q,hC,hq,hquad,hcorr⟩ := normalized_local_quadratic_inverse h2 f hf hδ hU
  exact ⟨C,q,(by exact_mod_cast hC : (C.card : ℝ) ≤ normalizedRank δ).trans
    (normalizedRank_power_bound hδ hδ1),hq,hquad,(normalizedCorrelation_power_lower hδ hδ1).trans hcorr⟩

#print axioms polynomial_normalized_local_quadratic_inverse
end Erdos3NormalizedQuadraticPowerBounds
