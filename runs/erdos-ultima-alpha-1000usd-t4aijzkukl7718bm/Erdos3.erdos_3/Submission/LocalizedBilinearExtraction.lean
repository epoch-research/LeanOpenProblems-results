import Submission.LocalBilinearExtraction

/-! Localizing the extracted frequencies to a single Bohr neighborhood. The
result retains a fixed shift and a fixed character offset in the derivative
correlations; these offsets must not be silently discarded. -/
namespace Erdos3LocalizedBilinearExtraction
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3LocalBilinearExtraction
  Erdos3FreimanFrequencyGraph Erdos3FiniteBohr
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A localized pre-inverse form with explicit rank and cardinality losses.
The character-valued map is locally additive, but no symmetry or integrated
quadratic phase is asserted. -/
theorem large_U3_localized_bilinear (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ D : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
    ∃ T : Finset G, ∃ a₀ : G, ∃ χ₀ : AddChar G ℂ,
      0 ∈ T ∧ T ⊆ bohr D (1/2) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        extractionLoss δ*(17 : ℝ)^(2*D.card)*(T.card : ℝ) ∧
      (D.card : ℝ) ≤ rankBound δ ∧ F 0 = 0 ∧
      (∀ x ∈ bohr D (1/2), ∀ y ∈ bohr D (1/2),
        x+y ∈ bohr D (1/2) → F (x+y) = F x+F y) ∧
      (∀ t ∈ T, δ/2 ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2) := by
  obtain ⟨H,ξ,D,F,hH,hsize,hcoef,hD,hF0,hFdiff,hFadd⟩ := large_U3_local_bilinear f hf hδ hU
  let U := bohr D (1/4)
  have hU : U.Nonempty := ⟨0,bohr_zero D (by norm_num)⟩
  have hcardU : Fintype.card G ≤ 17^(2*D.card)*U.card := by
    simpa only [show 2*8+1 = 17 by decide,show (2 : ℝ)/(8 : ℕ) = 1/4 by norm_num] using
      card_bohr_lower D (q := 8) (by decide)
  obtain ⟨η,hη⟩ := exists_large_translate_fiber H id U hU hcardU
  let H' := H.filter (fun h ↦ h-η ∈ U)
  have hcount : H.card ≤ 17^(2*D.card)*H'.card := hη
  have hH' : H'.Nonempty := by
    apply card_pos.mp
    by_contra hn
    have hz : H'.card = 0 := by omega
    rw [hz,mul_zero] at hcount
    have hp := hH.card_pos
    omega
  obtain ⟨a₀,ha₀⟩ := hH'
  let T := H'.image (fun h ↦ h-a₀)
  have hcT : T.card = H'.card := card_image_of_injective _ (fun _ _ hh ↦ sub_left_injective hh)
  have hT0 : (0 : G) ∈ T := mem_image.mpr ⟨a₀,ha₀,sub_self _⟩
  have hTsub : T ⊆ bohr D (1/2) := by
    intro t ht
    obtain ⟨h,hh,rfl⟩ := mem_image.mp ht
    have h1 : h-η ∈ bohr D (1/4) := (mem_filter.mp hh).2
    have h2 : a₀-η ∈ bohr D (1/4) := (mem_filter.mp ha₀).2
    have h3 := bohr_add h1 (bohr_neg h2)
    have he : (h-η)+-(a₀-η) = h-a₀ := by abel
    rw [he,show (1/4 : ℝ)+1/4 = 1/2 by norm_num] at h3
    exact h3
  have hcountR : (H.card : ℝ) ≤ (17 : ℝ)^(2*D.card)*(T.card : ℝ) := by
    rw [hcT]
    exact_mod_cast hcount
  have hLoss : 0 ≤ extractionLoss δ := by unfold extractionLoss; positivity
  refine ⟨D,F,T,a₀,ξ a₀,hT0,hTsub,?_,hD,hF0,hFadd,?_⟩
  · exact hsize.trans ((mul_le_mul_of_nonneg_left hcountR hLoss).trans_eq (by ring))
  · intro t ht
    obtain ⟨h,hh,rfl⟩ := mem_image.mp ht
    have he := hFdiff h (mem_filter.mp hh).1 a₀ (mem_filter.mp ha₀).1
    rw [he,sub_add_cancel,sub_add_cancel]
    exact hcoef h (mem_filter.mp hh).1

#print axioms large_U3_localized_bilinear
end Erdos3LocalizedBilinearExtraction
