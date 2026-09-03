import Submission.U3LocalQuadraticCorrelation

/-! Packaging the local U³ inverse result with an explicit eight-vertex cube
identity for its phase. The phase is genuinely quadratic on the whole local
correlation domain, not just on selected derivative pairs. -/
namespace Erdos3LocalQuadraticInverse
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3LocalQuadraticIntegration Erdos3DoubledBohrLocalization Erdos3LocalBilinearExtraction
  Erdos3QuantitativeSkewSymmetry Erdos3CorrelationSifting Erdos3U3LocalQuadraticCorrelation
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Quadraticity is tested on every cube whose eight vertices belong to R. -/
def IsLocallyQuadratic (R : Set G) (q : G → ℂ) : Prop :=
  ∀ x h k l : G,
    x ∈ R → x+h ∈ R → x+k ∈ R → (x+k)+h ∈ R →
    x+l ∈ R → (x+l)+h ∈ R → (x+l)+k ∈ R → ((x+l)+k)+h ∈ R →
    derivative (derivative (derivative q h) k) l x = 1

lemma integrated_phase_local_quadratic (B : Finset (AddChar G ℂ))
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (bohr B (1/2) : Set G) F)
    (half : G →+ G) {R : Set G} (hR : R ⊆ (bohr B (1/4) : Set G)) :
    IsLocallyQuadratic R (Erdos3LocalQuadraticIntegration.quadraticPhase F half) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  have hsmall := bohr_mono B (by norm_num : (1/4 : ℝ) ≤ 1/2)
  have hh : h ∈ bohr B (1/2) := by
    have ht := bohr_add (hR hxh) (bohr_neg (hR hx))
    simpa only [show (1/4 : ℝ)+1/4 = 1/2 by norm_num,
      show (x+h)+-x = h by abel] using ht
  have hk : k ∈ bohr B (1/2) := by
    have ht := bohr_add (hR hxk) (bohr_neg (hR hx))
    simpa only [show (1/4 : ℝ)+1/4 = 1/2 by norm_num,
      show (x+k)+-x = k by abel] using ht
  exact quadraticPhase_third_derivative hF half hh hk
    (hsmall (hR hx)) (hsmall (hR hxh)) (hsmall (hR hxk)) (hsmall (hR hxkh))
    (hsmall (hR hxl)) (hsmall (hR hxlh)) (hsmall (hR hxlk)) (hsmall (hR hxlkh))

lemma derivative_mul_character (q : G → ℂ) (χ : AddChar G ℂ) (h x : G) :
    derivative (fun y ↦ q y*χ y) h x = χ h*derivative q h x := by
  have he : derivative (fun y ↦ q y*χ y) h x = derivative q h x*derivative χ h x := by
    simp only [derivative,map_mul]
    ring
  rw [he,derivative_char,mul_comm]

lemma second_derivative_mul_character (q : G → ℂ) (χ : AddChar G ℂ) (h k x : G) :
    derivative (derivative (fun y ↦ q y*χ y) h) k x = derivative (derivative q h) k x := by
  have he : derivative (fun y ↦ q y*χ y) h = fun y ↦ χ h*derivative q h y := by
    funext y
    exact derivative_mul_character q χ h y
  rw [he]
  exact derivative_unit_scale (derivative q h) (AddChar.norm_apply χ h) k x

lemma IsLocallyQuadratic.mul_character {R : Set G} {q : G → ℂ}
    (hq : IsLocallyQuadratic R q) (χ : AddChar G ℂ) :
    IsLocallyQuadratic R (fun y ↦ q y*χ y) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  have he : derivative (derivative (fun y ↦ q y*χ y) h) k = derivative (derivative q h) k := by
    funext y
    exact second_derivative_mul_character q χ h k y
  rw [he]
  exact hq x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh

lemma refined_doubled_subset (B E : Finset (AddChar G ℂ)) :
    doubledBohr (B ∪ E) (1/8) ⊆ bohr B (1/4) := by
  intro x hx
  have hh : x ∈ bohr (B ∪ E) (1/4) := by
    simpa only [show (2 : ℝ)*(1/8) = 1/4 by norm_num] using doubledBohr_subset (B ∪ E) (1/8) hx
  exact mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hh χ (mem_union_left _ hχ))

/-- A quantitative local inverse theorem for U³ in odd finite abelian groups.
The phase has norm one and vanishing third derivative on every local cube.
This remains a U³ theorem, not an all-order inverse or a density increment. -/
theorem local_quadratic_inverse (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ B E : Finset (AddChar G ℂ), ∃ T : Finset G, ∃ q : G → ℂ, ∃ a : G,
      0 ∈ T ∧ T ⊆ bohr B (1/16) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        extractionLoss δ*(129 : ℝ)^(2*B.card)*(T.card : ℝ) ∧
      (B.card : ℝ) ≤ rankBound δ ∧
      (E.card : ℝ) ≤ symmetryRank (density T) ((δ/2)^8*(density T)^4) (δ/16) ∧
      (∀ x, ‖q x‖ = 1) ∧ IsLocallyQuadratic (doubledBohr (B ∪ E) (1/8) : Set G) q ∧
      δ*density T/(8*(8385 : ℝ)^(2*(B ∪ E).card)) ≤
        ‖𝔼 y, if y ∈ doubledBohr (B ∪ E) (1/8) then f (a+y)*conj (q y) else 0‖^2 := by
  obtain ⟨B,E,F,T,a,χ,hT0,hTsub,hsize,hB,hF0,hadd,hE,hEsub,hcorr⟩ :=
    large_U3_local_quadratic_correlation h2 f hf hδ hU
  let q : G → ℂ := fun y ↦ Erdos3LocalQuadraticIntegration.quadraticPhase F (halfHom h2) y*χ y
  have hq (x : G) : ‖q x‖ = 1 := by
    simp only [q,norm_mul,quadraticPhase_norm,AddChar.norm_apply,mul_one]
  have hquad : IsLocallyQuadratic (doubledBohr (B ∪ E) (1/8) : Set G) q :=
    (integrated_phase_local_quadratic B F hadd (halfHom h2) (refined_doubled_subset B E)).mul_character χ
  refine ⟨B,E,T,q,a,hT0,hTsub,hsize,hB,hE,hq,hquad,?_⟩
  simpa only [q,map_mul,mul_assoc] using hcorr

#print axioms local_quadratic_inverse
end Erdos3LocalQuadraticInverse
