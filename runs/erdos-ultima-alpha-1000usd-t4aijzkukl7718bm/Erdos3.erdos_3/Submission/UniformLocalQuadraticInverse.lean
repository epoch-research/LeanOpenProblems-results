import Submission.LocalQuadraticInverse

/-! A uniform-in-the-ambient-group quantitative local U³ inverse theorem.
All rank and correlation parameters here depend only on the U³ lower bound. -/
namespace Erdos3UniformLocalQuadraticInverse
open Finset Erdos3FiniteUniformity Erdos3FiniteBohr Erdos3LocalBilinearExtraction
  Erdos3QuantitativeSkewSymmetry Erdos3DoubledBohrLocalization
  Erdos3LocalQuadraticInverse Erdos3CorrelationSifting
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def baseRank (δ : ℝ) : ℕ := ⌈rankBound δ⌉₊
noncomputable def baseDensity (δ : ℝ) : ℝ :=
  δ^5/(256*extractionLoss δ*(129 : ℝ)^(2*baseRank δ))
noncomputable def inverseRank (δ : ℝ) : ℕ := baseRank δ+
  ⌈symmetryRank (baseDensity δ) ((δ/2)^8*(baseDensity δ)^4) (δ/16)⌉₊
noncomputable def inverseCorrelation (δ : ℝ) : ℝ :=
  δ*baseDensity δ/(8*(8385 : ℝ)^(2*inverseRank δ))

lemma baseDensity_pos {δ : ℝ} (hδ : 0 < δ) : 0 < baseDensity δ := by
  unfold baseDensity extractionLoss
  positivity

lemma inverseCorrelation_pos {δ : ℝ} (hδ : 0 < δ) : 0 < inverseCorrelation δ := by
  unfold inverseCorrelation
  exact div_pos (mul_pos hδ (baseDensity_pos hδ)) (by positivity)

lemma symmetrySamples_antitone {σ₀ σ₁ Λ₀ Λ₁ ε : ℝ}
    (hσ₀ : 0 < σ₀) (hσ : σ₀ ≤ σ₁) (hΛ₀ : 0 < Λ₀) (hΛ : Λ₀ ≤ Λ₁) (hε : 0 < ε) :
    symmetrySamples σ₁ Λ₁ ε ≤ symmetrySamples σ₀ Λ₀ ε := by
  unfold symmetrySamples
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  have hden : σ₀*(Λ₀/2)^4*(ε/8)^2 ≤ σ₁*(Λ₁/2)^4*(ε/8)^2 := by
    gcongr <;> linarith
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

lemma symmetryRank_antitone {σ₀ σ₁ Λ₀ Λ₁ ε : ℝ}
    (hσ₀ : 0 < σ₀) (hσ : σ₀ ≤ σ₁) (hσ₁ : σ₁ ≤ 1)
    (hΛ₀ : 0 < Λ₀) (hΛ : Λ₀ ≤ Λ₁) (hε : 0 < ε) :
    symmetryRank σ₁ Λ₁ ε ≤ symmetryRank σ₀ Λ₀ ε := by
  have hn := symmetrySamples_antitone hσ₀ hσ hΛ₀ hΛ hε
  have hexp : 2*(symmetrySamples σ₁ Λ₁ ε+1) ≤ 2*(symmetrySamples σ₀ Λ₀ ε+1) := by omega
  have hpow : σ₀^(2*(symmetrySamples σ₀ Λ₀ ε+1)) ≤ σ₁^(2*(symmetrySamples σ₁ Λ₁ ε+1)) :=
    (pow_le_pow_of_le_one hσ₀.le (hσ.trans hσ₁) hexp).trans (pow_le_pow_left₀ hσ₀.le hσ _)
  have hprod : (Λ₀*σ₀)^2 ≤ (Λ₁*σ₁)^2 := by
    exact pow_le_pow_left₀ (mul_nonneg hΛ₀.le hσ₀.le)
      (mul_le_mul hΛ hσ hσ₀.le (hΛ₀.le.trans hΛ)) 2
  exact add_le_add
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow)
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod)

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma baseDensity_le_support (B : Finset (AddChar G ℂ)) (T : Finset G)
    {δ : ℝ} (hδ : 0 < δ) (hB : (B.card : ℝ) ≤ rankBound δ)
    (hsize : δ^5/256*(Fintype.card G : ℝ) ≤ extractionLoss δ*(129 : ℝ)^(2*B.card)*(T.card : ℝ)) :
    baseDensity δ ≤ density T := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hBc : B.card ≤ baseRank δ := by
    exact_mod_cast hB.trans (Nat.le_ceil (rankBound δ))
  have hL : 0 < extractionLoss δ := by unfold extractionLoss; positivity
  have hh : δ^5/256 ≤ extractionLoss δ*(129 : ℝ)^(2*B.card)*density T := by
    unfold density
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hN).mpr hsize
  have hpow : (129 : ℝ)^(2*B.card) ≤ (129 : ℝ)^(2*baseRank δ) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 hBc)
  have hupper := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hL.le) (density_nonneg T)
  apply (div_le_iff₀ (by positivity : 0 < 256*extractionLoss δ*(129 : ℝ)^(2*baseRank δ))).mpr
  nlinarith only [hh.trans hupper]

/-- Explicit parameters depending only on delta give a local quadratic inverse
in every finite abelian group where doubling is bijective. -/
theorem uniform_local_quadratic_inverse (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → ℂ, ∃ a : G,
      C.card ≤ inverseRank δ ∧ (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (doubledBohr C (1/8) : Set G) q ∧
      inverseCorrelation δ ≤
        ‖𝔼 y, if y ∈ doubledBohr C (1/8) then f (a+y)*conj (q y) else 0‖^2 := by
  obtain ⟨B,E,T,q,a,hT0,hTsub,hsize,hB,hE,hq,hquad,hcorr⟩ := local_quadratic_inverse h2 f hf hδ hU
  have hσ : 0 < density T := density_pos T ⟨0,hT0⟩
  have hσ1 : density T ≤ 1 := by
    unfold density
    apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
    exact_mod_cast card_le_univ T
  have hβ := baseDensity_pos hδ
  have hβσ := baseDensity_le_support B T hδ hB hsize
  have hΛ₀ : 0 < (δ/2)^8*(baseDensity δ)^4 := by positivity
  have hΛ : (δ/2)^8*(baseDensity δ)^4 ≤ (δ/2)^8*(density T)^4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ.le hβσ 4) (by positivity)
  have hskew := symmetryRank_antitone hβ hβσ hσ1 hΛ₀ hΛ (by positivity : 0 < δ/16)
  have hBc : B.card ≤ baseRank δ := by
    exact_mod_cast hB.trans (Nat.le_ceil (rankBound δ))
  have hEc : E.card ≤ ⌈symmetryRank (baseDensity δ) ((δ/2)^8*(baseDensity δ)^4) (δ/16)⌉₊ := by
    exact_mod_cast (hE.trans hskew).trans (Nat.le_ceil _)
  have hC : (B ∪ E).card ≤ inverseRank δ := (card_union_le B E).trans (Nat.add_le_add hBc hEc)
  have hpow : 8*(8385 : ℝ)^(2*(B ∪ E).card) ≤ 8*(8385 : ℝ)^(2*inverseRank δ) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 hC)
  have hl : inverseCorrelation δ ≤ δ*density T/(8*(8385 : ℝ)^(2*(B ∪ E).card)) := by
    calc
      _ ≤ δ*density T/(8*(8385 : ℝ)^(2*inverseRank δ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβσ hδ.le) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hδ.le hσ.le) (by positivity) hpow
  exact ⟨B ∪ E,q,a,hC,hq,hquad,hl.trans hcorr⟩

lemma doubledBohr_eq_bohr_pullback (h2 : Function.Bijective (fun x : G ↦ x+x))
    (C : Finset (AddChar G ℂ)) (r : ℝ) :
    doubledBohr C r = bohr (C.image (fun χ ↦ χ.compAddMonoidHom (Erdos3LocalQuadraticIntegration.halfHom h2))) r := by
  ext x
  rw [mem_doubledBohr h2,mem_bohr,mem_bohr]
  constructor
  · intro hx ψ hψ
    obtain ⟨χ,hχ,rfl⟩ := mem_image.mp hψ
    exact hx χ hχ
  · intro hx χ hχ
    exact hx _ (mem_image.mpr ⟨χ,hχ,rfl⟩)

/-- The doubled domain is itself an ordinary Bohr set after pulling back its
characters along halving. This is the usual Bohr-domain form of the inverse theorem. -/
theorem bohr_local_quadratic_inverse (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → ℂ, ∃ a : G,
      C.card ≤ inverseRank δ ∧ (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (bohr C (1/8) : Set G) q ∧
      inverseCorrelation δ ≤
        ‖𝔼 y, if y ∈ bohr C (1/8) then f (a+y)*conj (q y) else 0‖^2 := by
  obtain ⟨C,q,a,hC,hq,hquad,hcorr⟩ := uniform_local_quadratic_inverse h2 f hf hδ hU
  rw [doubledBohr_eq_bohr_pullback h2] at hquad hcorr
  exact ⟨_,q,a,card_image_le.trans hC,hq,hquad,hcorr⟩

#print axioms uniform_local_quadratic_inverse
#print axioms bohr_local_quadratic_inverse
end Erdos3UniformLocalQuadraticInverse
