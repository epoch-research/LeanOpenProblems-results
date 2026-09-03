import Submission.TwistedCorrelationEnergy

/-! Local extraction with difference-compatible frequencies, and phase-preserving
duality for the aligned mixed derivative correlations. -/
namespace Erdos3LocalPhaseDuality
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3LocalBilinearExtraction
  Erdos3FreimanFrequencyGraph Erdos3FiniteBohr Erdos3TwistedCorrelationEnergy
  Erdos3SpectralGraphEnergy
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 4500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A localized pre-inverse form with explicit rank and cardinality losses.
The character-valued map is locally additive, but no symmetry or integrated
quadratic phase is asserted. -/
theorem large_U3_compatible_bilinear (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ D : Finset (AddChar G ℂ), ∃ F : G → AddChar G ℂ,
    ∃ T : Finset G, ∃ a₀ : G, ∃ χ₀ : AddChar G ℂ,
      0 ∈ T ∧ T ⊆ bohr D (1/2) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        extractionLoss δ*(17 : ℝ)^(2*D.card)*(T.card : ℝ) ∧
      (D.card : ℝ) ≤ rankBound δ ∧ F 0 = 0 ∧
      (∀ x ∈ bohr D (1/2), ∀ y ∈ bohr D (1/2),
        x+y ∈ bohr D (1/2) → F (x+y) = F x+F y) ∧
      (∀ h ∈ T, ∀ k ∈ T, F (h-k) = F h-F k) ∧
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

lemma shifted_mixed_coefficient (f : G → ℂ) (a₀ : G) (χ₀ : AddChar G ℂ)
    (F : G → AddChar G ℂ) (t : G) :
    mixedCoefficient (fun x ↦ f (x+a₀)) (fun x ↦ f x*χ₀ x) F t =
      hat (derivative f (t+a₀)) (F t+χ₀) := by
  unfold mixedCoefficient hat derivative
  apply expect_congr rfl
  intro x _
  simp only [AddChar.add_apply,map_mul,add_assoc]
  ring

lemma mixedCoefficient_norm_le_one (u v : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (h : G) :
    ‖mixedCoefficient u v F h‖ ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro x _
  simp only [norm_mul,Complex.norm_conj,AddChar.norm_apply,mul_one]
  exact (mul_le_mul (hu _) (hv _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- Aligning the large mixed coefficients produces a one-bounded function on T
whose derivatives have substantial average Fourier energy at the opposite
frequency assignment. No symmetry is deduced merely from this bound. -/
theorem aligned_phase_duality (T : Finset G) (u v : G → ℂ) (F : G → AddChar G ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1)
    (hF : ∀ h ∈ T, ∀ k ∈ T, F (h-k) = F h-F k)
    {κ : ℝ} (hκ : 0 ≤ κ) (hc : ∀ t ∈ T, κ ≤ ‖mixedCoefficient u v F t‖^2) :
    ∃ b : G → ℂ, (∀ t, ‖b t‖ ≤ 1) ∧ (∀ t, t ∉ T → b t = 0) ∧
      (κ*((T.card : ℝ)/(Fintype.card G : ℝ)))^4 ≤
        𝔼 a, ‖hat (derivative b a) (-F a)‖^2 := by
  let c : G → ℂ := mixedCoefficient u v F
  have hnorm (t : G) : ‖c t‖ ≤ 1 := mixedCoefficient_norm_le_one u v F hu hv t
  have hlarge (t : G) (ht : t ∈ T) : κ ≤ ‖c t‖ := by
    have hh := hc t ht
    change κ ≤ ‖c t‖^2 at hh
    nlinarith [hnorm t,norm_nonneg (c t)]
  have halign (t : G) := exists_phase_alignment (c t)
  choose d hd hdc using halign
  let b : G → ℂ := fun t ↦ if t ∈ T then d t else 0
  have hb (t : G) : ‖b t‖ ≤ 1 := by
    dsimp [b]
    split_ifs
    · exact hd t
    · norm_num
  have hzero (t : G) (ht : t ∉ T) : b t = 0 := if_neg ht
  have he : (𝔼 t, b t*c t) = ((𝔼 t, if t ∈ T then ‖c t‖ else 0 : ℝ) : ℂ) := by
    rw [ofReal_expect]
    apply expect_congr rfl
    intro t _
    by_cases ht : t ∈ T
    · simp only [b,if_pos ht,hdc]
    · simp only [b,if_neg ht,zero_mul,Complex.ofReal_zero]
  have hmean0 : 0 ≤ 𝔼 t, if t ∈ T then ‖c t‖ else 0 :=
    expect_nonneg (fun _ _ ↦ by split_ifs <;> positivity)
  have hmean : κ*((T.card : ℝ)/(Fintype.card G : ℝ)) ≤ 𝔼 t, if t ∈ T then ‖c t‖ else 0 := by
    have hh : (𝔼 t : G, if t ∈ T then κ else 0) ≤ 𝔼 t, if t ∈ T then ‖c t‖ else 0 := by
      apply expect_le_expect
      intro t _
      split_ifs with ht
      · exact hlarge t ht
      · exact le_rfl
    have hleft : (𝔼 t : G, if t ∈ T then κ else 0) = κ*((T.card : ℝ)/(Fintype.card G : ℝ)) := by
      simp [Fintype.expect_eq_sum_div_card,mul_div_assoc,mul_comm]
    rwa [hleft] at hh
  have hh := mixed_correlation_fourth_le T b u v F hu hv hzero hF
  change ‖𝔼 t, b t*c t‖^4 ≤ _ at hh
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hmean0] at hh
  exact ⟨b,hb,hzero,(pow_le_pow_left₀ (by positivity) hmean 4).trans hh⟩

#print axioms large_U3_compatible_bilinear
#print axioms aligned_phase_duality
end Erdos3LocalPhaseDuality
