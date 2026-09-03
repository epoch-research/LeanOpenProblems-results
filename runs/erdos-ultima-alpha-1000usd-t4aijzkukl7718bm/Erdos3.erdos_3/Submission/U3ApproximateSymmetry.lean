import Submission.QuantitativeSkewSymmetry

/-! Large U³ yields a quantitative Bohr domain of approximate symmetry for the
extracted frequency map. Both derivative-correlation offsets are retained. -/
namespace Erdos3U3ApproximateSymmetry
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3LocalBilinearExtraction
  Erdos3FreimanFrequencyGraph Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3LocalPhaseDuality Erdos3AveragedAntisymmetry Erdos3BiasedSkewDifferences
  Erdos3LocalQuadraticIntegration Erdos3QuantitativeSkewSymmetry
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Deeper localization leaves room for the eight-term domain checks in
local symmetry extraction. -/
theorem large_U3_deep_bilinear (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ D : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
    ∃ T : Finset G, ∃ a₀ : G, ∃ χ₀ : AddChar G ℂ,
      0 ∈ T ∧ T ⊆ bohr D (1/16) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        extractionLoss δ*(129 : ℝ)^(2*D.card)*(T.card : ℝ) ∧
      (D.card : ℝ) ≤ rankBound δ ∧ F 0 = 0 ∧
      (∀ x ∈ bohr D (1/2), ∀ y ∈ bohr D (1/2),
        x+y ∈ bohr D (1/2) → F (x+y) = F x+F y) ∧
      (∀ h ∈ T, ∀ k ∈ T, F (h-k) = F h-F k) ∧
      (∀ t ∈ T, δ/2 ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2) := by
  obtain ⟨H,ξ,D,F,hH,hsize,hcoef,hD,hF0,hFdiff,hFadd⟩ := large_U3_local_bilinear f hf hδ hU
  let U := bohr D (1/32)
  have hU : U.Nonempty := ⟨0,bohr_zero D (by norm_num)⟩
  have hcardU : Fintype.card G ≤ 129^(2*D.card)*U.card := by
    simpa only [show 2*64+1 = 129 by decide,show (2 : ℝ)/(64 : ℕ) = 1/32 by norm_num] using
      card_bohr_lower D (q := 64) (by decide)
  obtain ⟨η,hη⟩ := exists_large_translate_fiber H id U hU hcardU
  let H' := H.filter (fun h ↦ h-η ∈ U)
  have hcount : H.card ≤ 129^(2*D.card)*H'.card := hη
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
  have hTsub : T ⊆ bohr D (1/16) := by
    intro t ht
    obtain ⟨h,hh,rfl⟩ := mem_image.mp ht
    have h1 : h-η ∈ bohr D (1/32) := (mem_filter.mp hh).2
    have h2 : a₀-η ∈ bohr D (1/32) := (mem_filter.mp ha₀).2
    have h3 := bohr_add h1 (bohr_neg h2)
    have he : (h-η)+-(a₀-η) = h-a₀ := by abel
    rw [he,show (1/32 : ℝ)+1/32 = 1/16 by norm_num] at h3
    exact h3
  have hcountR : (H.card : ℝ) ≤ (129 : ℝ)^(2*D.card)*(T.card : ℝ) := by
    rw [hcT]
    exact_mod_cast hcount
  have hLoss : 0 ≤ extractionLoss δ := by unfold extractionLoss; positivity
  refine ⟨D,F,T,a₀,ξ a₀,hT0,hTsub,?_,hD,hF0,hFadd,?_,?_⟩
  · exact hsize.trans ((mul_le_mul_of_nonneg_left hcountR hLoss).trans_eq (by ring))
  · intro h hh k hk
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hh
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hk
    rw [show (u-a₀)-(v-a₀) = u-v by abel,
      hFdiff u (mem_filter.mp hu).1 v (mem_filter.mp hv).1,
      hFdiff u (mem_filter.mp hu).1 a₀ (mem_filter.mp ha₀).1,
      hFdiff v (mem_filter.mp hv).1 a₀ (mem_filter.mp ha₀).1]
    abel
  · intro t ht
    obtain ⟨h,hh,rfl⟩ := mem_image.mp ht
    have he := hFdiff h (mem_filter.mp hh).1 a₀ (mem_filter.mp ha₀).1
    rw [he,sub_add_cancel,sub_add_cancel]
    exact hcoef h (mem_filter.mp hh).1


open Erdos3CorrelationSifting in
/-- An unconditional approximate-symmetry conclusion from large U³.
The rank cost is explicit in the retained support density, whose lower bound
is separately stated. This is not yet a quadratic correlation theorem. -/
theorem large_U3_approximate_symmetry (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) (hε : 0 < ε) :
    ∃ B E : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
    ∃ T : Finset G, ∃ a₀ : G, ∃ χ₀ : AddChar G ℂ,
      0 ∈ T ∧ T ⊆ bohr B (1/16) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        extractionLoss δ*(129 : ℝ)^(2*B.card)*(T.card : ℝ) ∧
      (B.card : ℝ) ≤ rankBound δ ∧ F 0 = 0 ∧
      LocallyAdditive (bohr B (1/2) : Set G) F ∧
      (∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t) ∧
      (∀ t ∈ T, δ/2 ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2) ∧
      (E.card : ℝ) ≤ symmetryRank (density T) ((δ/2)^8*(density T)^4) ε ∧
      bohr E (1/2) ⊆ bohr B (1/4) ∧
      ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ ε := by
  obtain ⟨B,F,T,a₀,χ₀,hT0,hTsub,hsize,hB,hF0,hadd,hdiff,hcoef⟩ :=
    large_U3_deep_bilinear f hf hδ hU
  have hT : T.Nonempty := ⟨0,hT0⟩
  have hσ : 0 < density T := Erdos3CorrelationSifting.density_pos T hT
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
  obtain ⟨E,hE,hEsub,hsym⟩ := exists_quantitative_bohr_symmetry B F hadd T hT hTsub hdiff
    (by positivity : 0 < (δ/2)^8*(density T)^4) hmean hε
  exact ⟨B,E,F,T,a₀,χ₀,hT0,hTsub,hsize,hB,hF0,hadd,hdiff,hcoef,hE,hEsub,hsym⟩

/-- On a slightly smaller refined Bohr domain, approximate symmetry supplies
the earlier conditional integration estimate. Doubling avoids a square-root
branch inference. No correlation with this phase is asserted here. -/
theorem integrated_derivative_on_refined_bohr (B E : Finset (AddChar G ℂ))
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (bohr B (1/2) : Set G) F)
    (half : G →+ G) (hhalf : ∀ x, half (x+x) = x)
    {ε : ℝ} (hsym : ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ ε)
    {u v : G} (hu : u ∈ bohr (B ∪ E) (1/8)) (hv : v ∈ bohr (B ∪ E) (1/8)) :
    ‖derivative (Erdos3LocalQuadraticIntegration.quadraticPhase F half) (v+v) (u+u)-
      Erdos3LocalQuadraticIntegration.quadraticPhase F half (v+v)*F (v+v) (u+u)‖ ≤ 2*ε := by
  have huB : u ∈ bohr B (1/8) := mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hu χ (mem_union_left _ hχ))
  have hvB : v ∈ bohr B (1/8) := mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hv χ (mem_union_left _ hχ))
  have huE : u ∈ bohr E (1/2) := bohr_mono E (by norm_num : (1/8 : ℝ) ≤ 1/2)
    (mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hu χ (mem_union_right _ hχ)))
  have hvE : v ∈ bohr E (1/2) := bohr_mono E (by norm_num : (1/8 : ℝ) ≤ 1/2)
    (mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hv χ (mem_union_right _ hχ)))
  have huu : u+u ∈ bohr B (1/4) := by
    simpa only [show (1/8 : ℝ)+1/8 = 1/4 by norm_num] using bohr_add huB huB
  have hvv : v+v ∈ bohr B (1/4) := by
    simpa only [show (1/8 : ℝ)+1/8 = 1/4 by norm_num] using bohr_add hvB hvB
  have hsum : (u+u)+(v+v) ∈ bohr B (1/2) := by
    simpa only [show (1/4 : ℝ)+1/4 = 1/2 by norm_num] using bohr_add huu hvv
  exact quadraticPhase_derivative_approx hF half hhalf
    (bohr_mono B (by norm_num : (1/8 : ℝ) ≤ 1/2) huB)
    (bohr_mono B (by norm_num : (1/8 : ℝ) ≤ 1/2) hvB)
    (bohr_mono B (by norm_num : (1/4 : ℝ) ≤ 1/2) huu)
    (bohr_mono B (by norm_num : (1/4 : ℝ) ≤ 1/2) hvv)
    hsum (hsym u huE v hvE)

#print axioms large_U3_approximate_symmetry
#print axioms integrated_derivative_on_refined_bohr
end Erdos3U3ApproximateSymmetry
