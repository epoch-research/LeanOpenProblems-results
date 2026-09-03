import Submission.CompatibleQuadraticCorrelation

/-! A sharper uniform local U³ inverse theorem. The input to symmetry now has
polynomial density; no exponential loss from early Bohr localization remains. -/
namespace Erdos3ReducedLossQuadraticInverse
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FiniteBohr
  Erdos3LocalQuadraticInverse Erdos3QuantitativeSkewSymmetry Erdos3DoubledBohrLocalization
  Erdos3UnlocalizedBilinearExtraction Erdos3UnlocalizedSkewSymmetry
  Erdos3CompatibleQuadraticCorrelation Erdos3UniformLocalQuadraticInverse Erdos3CorrelationSifting
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def retainedDensity (δ : ℝ) : ℝ := δ^5/(256*unlocalizedLoss δ)
noncomputable def reducedRank (δ : ℝ) : ℕ :=
  ⌈symmetryRank (retainedDensity δ) ((δ/2)^8*(retainedDensity δ)^4) (δ/16)⌉₊
noncomputable def reducedCorrelation (δ : ℝ) : ℝ :=
  δ*retainedDensity δ/(8*(8385 : ℝ)^(2*reducedRank δ))

lemma retainedDensity_pos {δ : ℝ} (hδ : 0 < δ) : 0 < retainedDensity δ := by
  unfold retainedDensity unlocalizedLoss
  positivity

lemma reducedCorrelation_pos {δ : ℝ} (hδ : 0 < δ) : 0 < reducedCorrelation δ := by
  unfold reducedCorrelation
  exact div_pos (mul_pos hδ (retainedDensity_pos hδ)) (by positivity)

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma retainedDensity_le_support (T : Finset G) {δ : ℝ} (hδ : 0 < δ)
    (hsize : δ^5/256*(Fintype.card G : ℝ) ≤ unlocalizedLoss δ*(T.card : ℝ)) :
    retainedDensity δ ≤ density T := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hL : 0 < unlocalizedLoss δ := by unfold unlocalizedLoss; positivity
  have hh : δ^5/256 ≤ unlocalizedLoss δ*density T := by
    unfold density
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hN).mpr hsize
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 256) hL)).mpr
  nlinarith only [hh]

/-- A quantitative local quadratic inverse with symmetry applied before any
exponential thinning of the direction set. The constants are uniform in |G|. -/
theorem reduced_loss_quadratic_inverse (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ C : Finset (AddChar G ℂ), ∃ q : G → ℂ, ∃ a : G,
      C.card ≤ reducedRank δ ∧ (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (bohr C (1/8) : Set G) q ∧
      reducedCorrelation δ ≤
        ‖𝔼 y, if y ∈ bohr C (1/8) then f (a+y)*conj (q y) else 0‖^2 := by
  have hδ1 : δ ≤ 1 := hU.trans (uniformityPower_le_one 2 f hf)
  obtain ⟨T,F,a₀,χ₀,E,hT0,hsize,hF0,hdiff,hcoef,hE,hadd,hsym⟩ :=
    large_U3_unlocalized_symmetry f hf hδ hU (by positivity : 0 < δ/16)
  have hT : T.Nonempty := ⟨0,hT0⟩
  obtain ⟨q,a,hq,hquad,hcorr⟩ := compatible_quadratic_correlation h2 f hf T hT F a₀ χ₀ E hadd hdiff
    (by positivity : 0 < δ/2) (by linarith : δ/2 ≤ 1) hcoef
    (by simpa only [show δ/2/8 = δ/16 by ring] using hsym)
  have hσ : 0 < density T := density_pos T hT
  have hσ1 : density T ≤ 1 := by
    unfold density
    apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
    exact_mod_cast card_le_univ T
  have hβ := retainedDensity_pos hδ
  have hβσ := retainedDensity_le_support T hδ hsize
  have hΛ₀ : 0 < (δ/2)^8*(retainedDensity δ)^4 := by positivity
  have hΛ : (δ/2)^8*(retainedDensity δ)^4 ≤ (δ/2)^8*(density T)^4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ.le hβσ 4) (by positivity)
  have hskew := symmetryRank_antitone hβ hβσ hσ1 hΛ₀ hΛ (by positivity : 0 < δ/16)
  have hEc : E.card ≤ reducedRank δ := by
    exact_mod_cast (hE.trans hskew).trans (Nat.le_ceil _)
  have hpow : 8*(8385 : ℝ)^(2*E.card) ≤ 8*(8385 : ℝ)^(2*reducedRank δ) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 hEc)
  have hl : reducedCorrelation δ ≤ (δ/2)*density T/(4*(8385 : ℝ)^(2*E.card)) := by
    calc
      _ ≤ δ*density T/(8*(8385 : ℝ)^(2*reducedRank δ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβσ hδ.le) (by positivity)
      _ ≤ δ*density T/(8*(8385 : ℝ)^(2*E.card)) :=
        div_le_div_of_nonneg_left (mul_nonneg hδ.le hσ.le) (by positivity) hpow
      _ = _ := by ring
  have hc := hl.trans hcorr
  rw [doubledBohr_eq_bohr_pullback h2] at hquad hc
  exact ⟨_,q,a,card_image_le.trans hEc,hq,hquad,hc⟩

#print axioms reduced_loss_quadratic_inverse
end Erdos3ReducedLossQuadraticInverse
