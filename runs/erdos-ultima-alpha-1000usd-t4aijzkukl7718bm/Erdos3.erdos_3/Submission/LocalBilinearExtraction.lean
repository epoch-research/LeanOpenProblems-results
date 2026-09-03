import Submission.FiniteBogolyubov

/-! Combining higher Freiman extraction, consistent difference extension, and
Bogolyubov gives a locally additive frequency map on an explicit Bohr set.
No symmetry or quadratic integration is claimed here. -/
namespace Erdos3LocalBilinearExtraction
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3HigherFreimanExtraction
  Erdos3HigherFreimanRestriction Erdos3LocalFreimanExtension Erdos3FiniteBogolyubov
  Erdos3FiniteBohr
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def extractionLoss (δ : ℝ) : ℝ := (2*(((2 : ℝ)^65/δ^41)^13+1))^196
noncomputable def rankBound (δ : ℝ) : ℝ := 8*(256*extractionLoss δ/δ^5)^2

/-- A six-Freiman map on H has a locally additive extension on a constant-radius
Bohr subset of 2H-2H, agreeing with all frequency differences from H-H. -/
theorem freiman_local_bilinear (H : Finset G) (hH : H.Nonempty) (ξ : G → AddChar G ℂ)
    (hξ : IsAddFreimanHom 6 (H : Set G) Set.univ ξ) :
    ∃ D : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
      (D.card : ℝ) ≤ 8/(density H)^2 ∧ F 0 = 0 ∧
      (∀ a ∈ H, ∀ b ∈ H, F (a-b) = ξ a-ξ b) ∧
      (∀ x ∈ bohr D (1/2), ∀ y ∈ bohr D (1/2),
        x+y ∈ bohr D (1/2) → F (x+y) = F x+F y) := by
  obtain ⟨F,hF0,hFdiff,hFadd⟩ := exists_local_additive_extension H 2 (by decide) ξ hξ
  obtain ⟨D,hD,_,hsub⟩ := bogolyubov H hH
  exact ⟨D,F,hD,hF0,hFdiff,fun _ hx _ hy hxy ↦ hFadd _ (hsub hx) _ (hsub hy) (hsub hxy)⟩

/-- Large U³ produces a polynomially bounded-rank local frequency map. It is
additive locally in its first argument and, as a character, globally additive
in its second argument. No unjustified symmetry assertion is included. -/
theorem large_U3_local_bilinear (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ H : Finset G, ∃ ξ : G → AddChar G ℂ,
    ∃ D : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
      H.Nonempty ∧
      δ^5/256*(Fintype.card G : ℝ) ≤ extractionLoss δ*(H.card : ℝ) ∧
      (∀ h ∈ H, δ/2 ≤ ‖hat (derivative f h) (ξ h)‖^2) ∧
      (D.card : ℝ) ≤ rankBound δ ∧ F 0 = 0 ∧
      (∀ a ∈ H, ∀ b ∈ H, F (a-b) = ξ a-ξ b) ∧
      (∀ x ∈ bohr D (1/2), ∀ y ∈ bohr D (1/2),
        x+y ∈ bohr D (1/2) → F (x+y) = F x+F y) := by
  obtain ⟨H,ξ,hH,hFreiman,hcoef,hsize⟩ := large_U3_higher_freiman_graph 6 (by decide) f hf hδ hU
  change δ^5/256*(Fintype.card G : ℝ) ≤ extractionLoss δ*(H.card : ℝ) at hsize
  obtain ⟨D,F,hD,hF0,hFdiff,hFadd⟩ := freiman_local_bilinear H hH ξ hFreiman
  have hα : 0 < density H := density_pos H hH
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hαbound : δ^5/256 ≤ extractionLoss δ*density H := by
    unfold density
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hN).mpr hsize
  have hinv : 1/density H ≤ 256*extractionLoss δ/δ^5 := by
    apply (le_div_iff₀ (pow_pos hδ 5)).mpr
    rw [show 1/density H*δ^5 = δ^5/density H by ring]
    apply (div_le_iff₀ hα).mpr
    nlinarith only [hαbound]
  have hrank : (D.card : ℝ) ≤ rankBound δ := by
    apply hD.trans
    unfold rankBound
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/density H) hinv 2
    calc
      _ = 8*(1/density H)^2 := by rw [div_pow,one_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  exact ⟨H,ξ,D,F,hH,hsize,hcoef,hrank,hF0,hFdiff,hFadd⟩

#print axioms freiman_local_bilinear
#print axioms large_U3_local_bilinear
end Erdos3LocalBilinearExtraction
