import Submission.SingleExponentialQuadraticInverse
import Submission.UniformityCounting

/-! The four-form counting lemma combined with the quantitative local U³ inverse.
This gives quadratic structure for four-pattern-free sets, not a density increment. -/
namespace Erdos3FourPatternQuadraticStructure
open Erdos3SingleExponentialQuadraticInverse Erdos3UniformityCounting
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr
  Erdos3CorrelationSifting Erdos3LocalQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def fourRankConstant : ℝ := rankConstant*((8 : ℝ)^8)^33407388
noncomputable def fourCorrelationConstant : ℝ := correlationConstant*((8 : ℝ)^8)^33407388

lemma threshold_power (α : ℝ) :
    (1/((α^4/8)^8))^33407388 = ((8 : ℝ)^8)^33407388*(1/α)^1069036416 := by
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul,← inv_pow,mul_pow,← pow_mul]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma balanced_indicator_one_bounded (A : Finset F) :
    ∀ x, ‖((indicator A x-density A : ℝ) : ℂ)‖ ≤ 1 := by
  have hα : 0 ≤ density A := by unfold density; positivity
  have hα1 : density A ≤ 1 := by
    unfold density
    exact (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card F)).mpr
      (by exact_mod_cast Finset.card_le_univ A)
  intro x
  rw [Complex.norm_real,Real.norm_eq_abs]
  obtain ⟨hx0,hx1⟩ := indicator_norm_bounds A x
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Four-pattern-free sets of sufficient size have actual local quadratic
correlation. Both rank and logarithmic correlation loss are fixed powers of
inverse density, with explicit absolute constants. -/
theorem four_pattern_free_quadratic_correlation
    (h2 : Function.Bijective (fun x : F ↦ x+x))
    (v : Fin 4 → F) (hv : Function.Injective v) (A : Finset F) (hA : A.Nonempty)
    (hsize : 4 ≤ (density A)^3*(Fintype.card F : ℝ))
    (hdiag : ∀ x d : F, (∀ i : Fin 4, x+v i*d ∈ A) → d = 0) :
    ∃ C : Finset (AddChar F ℂ), ∃ q : F → ℂ, ∃ a : F,
      (C.card : ℝ) ≤ fourRankConstant*(1/density A)^1069036416 ∧
      (∀ x, ‖q x‖ = 1) ∧ IsLocallyQuadratic (bohr C (1/8) : Set F) q ∧
      Real.exp (-fourCorrelationConstant*(1/density A)^1069036416) ≤
        ‖𝔼 y, if y ∈ bohr C (1/8) then
          (((indicator A (a+y)-density A : ℝ) : ℂ))*conj (q y) else 0‖^2 := by
  have hα := density_pos A hA
  have hU := pattern_free_uniformity_lower 2 v hv A hA hsize hdiag
  have hU' : ((density A)^4/8)^8 ≤
      uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)) := by
    simpa only [show 2+2 = 4 from rfl,show 2^(2+1) = 8 from rfl,
      show (2 : ℝ)*(4 : ℕ) = 8 by norm_num] using hU.le
  obtain ⟨C,q,a,hC,hq,hquad,hcorr⟩ := single_exponential_local_quadratic_inverse h2
    (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)) (balanced_indicator_one_bounded A)
    (by positivity : 0 < ((density A)^4/8)^8) hU'
  rw [threshold_power] at hC hcorr
  refine ⟨C,q,a,?_,hq,hquad,?_⟩
  · simpa only [fourRankConstant,mul_assoc] using hC
  · simpa only [fourCorrelationConstant,neg_mul,mul_assoc] using hcorr

#print axioms four_pattern_free_quadratic_correlation
end Erdos3FourPatternQuadraticStructure
