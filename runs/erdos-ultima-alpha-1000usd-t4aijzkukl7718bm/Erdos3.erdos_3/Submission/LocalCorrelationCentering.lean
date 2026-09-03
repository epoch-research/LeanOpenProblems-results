import Submission.BohrLocalAverages
import Submission.WeightedCorrelation

/-! Approximate centering of correlations and convolutions relative to a stable local set.
These are localization ingredients, not the original Erdős conjecture. -/
namespace Erdos3LocalCorrelationCentering
open Finset Erdos3FiniteBohr Erdos3BohrTranslation Erdos3BohrLocalAverages
  Erdos3CorrelationSifting Erdos3CorrelationMoments Erdos3WeightedCorrelation
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def crossCorr (f g : G → ℝ) (t : G) : ℝ := 𝔼 x : G, f x*g (x+t)
noncomputable def crossConv (f g : G → ℝ) (t : G) : ℝ := 𝔼 x : G, f x*g (t-x)

lemma crossCorr_symm (f g : G → ℝ) (t : G) : crossCorr f g t = crossCorr g f (-t) :=
  Fintype.expect_equiv (Equiv.addRight t) _ _ (fun x ↦ by simp [mul_comm])

lemma crossConv_comm (f g : G → ℝ) (t : G) : crossConv f g t = crossConv g f t :=
  Fintype.expect_equiv (Equiv.subLeft t) _ _ (fun x ↦ by simp [mul_comm])

lemma crossConv_eq_crossCorr (f g : G → ℝ) (hg : ∀ x, g (-x) = g x) (t : G) :
    crossConv f g t = crossCorr f g (-t) := by
  unfold crossConv crossCorr
  apply expect_congr rfl
  intro x _
  rw [show t-x = -(x+ -t) by abel, hg]

lemma corr_sub_eq (f g : G → ℝ) (t : G) :
    corr (fun x ↦ f x-g x) t = corr f t-crossCorr f g t-crossCorr g f t+corr g t := by
  have he (x : G) : (f x-g x)*(f (x+t)-g (x+t)) =
      f x*f (x+t)-f x*g (x+t)-g x*f (x+t)+g x*g (x+t) := by ring
  unfold corr crossCorr
  simp_rw [he, expect_add_distrib, expect_sub_distrib]

lemma conv_sub_eq (f g : G → ℝ) (t : G) :
    conv (fun x ↦ f x-g x) t = conv f t-2*crossConv f g t+conv g t := by
  have he (x : G) : (f x-g x)*(f (t-x)-g (t-x)) =
      f x*f (t-x)-f x*g (t-x)-g x*f (t-x)+g x*g (t-x) := by ring
  have hcross : (𝔼 x : G, g x*f (t-x)) = 𝔼 x : G, f x*g (t-x) := crossConv_comm g f t
  unfold conv crossConv
  simp_rw [he, expect_add_distrib, expect_sub_distrib, hcross]
  ring

lemma indicator_translation_bound (B : Finset G) (hB : B.Nonempty) {δ : ℝ} (t : G)
    (ht : (𝔼 x : G, |normalized B (x+t)-normalized B x|) ≤ δ) :
    (𝔼 x : G, |indicator B (x+t)-indicator B x|) ≤ δ*density B := by
  have hβ := density_pos B hB
  have he (x : G) : |normalized B (x+t)-normalized B x| =
      |indicator B (x+t)-indicator B x|/density B := by
    rw [normalized, normalized, ← sub_div, abs_div, abs_of_pos hβ]
  simp_rw [he] at ht
  rw [← expect_div] at ht
  exact (div_le_iff₀ hβ).mp ht

lemma cross_indicator_close (B : Finset G) (hB : B.Nonempty) (f : G → ℝ)
    (hsupp : ∀ x, x ∉ B → f x = 0) {L δ : ℝ} (hL : 0 ≤ L) (hf : ∀ x, |f x| ≤ L)
    (t : G) (ht : (𝔼 x : G, |normalized B (x+t)-normalized B x|) ≤ δ) :
    |crossCorr f (indicator B) t-(𝔼 x : G, f x)| ≤ (δ*density B)*L := by
  have hind (x : G) : indicator B x*f x = f x := by
    by_cases hx : x ∈ B
    · simp [indicator, hx]
    · simp [indicator, hx, hsupp x hx]
  have h := weighted_translation_bound (indicator B) f hL hf t (indicator_translation_bound B hB t ht)
  simp only [hind] at h
  convert h using 1
  simp only [crossCorr, mul_comm]

/-- Centering by the local indicator approximates subtracting the local ambient mass. -/
theorem corr_center_local (B : Finset G) (hB : B.Nonempty) (f : G → ℝ)
    (hsupp : ∀ x, x ∉ B → f x = 0) (hmean : (𝔼 x : G, f x) = density B)
    {L δ : ℝ} (hL : 0 ≤ L) (hf : ∀ x, |f x| ≤ L) (t : G)
    (ht : (𝔼 x : G, |normalized B (x+t)-normalized B x|) ≤ δ)
    (hnt : (𝔼 x : G, |normalized B (x+ -t)-normalized B x|) ≤ δ) :
    |corr (fun x ↦ f x-indicator B x) t-(corr f t-density B)| ≤
      δ*density B*(2*L+1) := by
  have h₁ := cross_indicator_close B hB f hsupp hL hf t ht
  have h₂ := cross_indicator_close B hB f hsupp hL hf (-t) hnt
  rw [hmean] at h₁ h₂
  rw [← crossCorr_symm (indicator B) f t] at h₂
  have h₃ := cross_indicator_close B hB (indicator B) (fun x hx ↦ by simp [indicator, hx])
    (by norm_num : (0 : ℝ) ≤ 1) (indicator_abs_le_one B) t ht
  rw [expect_indicator, mul_one] at h₃
  change |corr (indicator B) t-density B| ≤ δ*density B at h₃
  rw [corr_sub_eq]
  rcases abs_le.mp h₁ with ⟨h₁l,h₁u⟩
  rcases abs_le.mp h₂ with ⟨h₂l,h₂u⟩
  rcases abs_le.mp h₃ with ⟨h₃l,h₃u⟩
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The corresponding convolution-centering estimate holds when the base indicator is even. -/
theorem conv_center_local (B : Finset G) (hB : B.Nonempty)
    (hBeven : ∀ x, indicator B (-x) = indicator B x) (f : G → ℝ)
    (hsupp : ∀ x, x ∉ B → f x = 0) (hmean : (𝔼 x : G, f x) = density B)
    {L δ : ℝ} (hL : 0 ≤ L) (hf : ∀ x, |f x| ≤ L) (t : G)
    (ht : (𝔼 x : G, |normalized B (x+t)-normalized B x|) ≤ δ)
    (hnt : (𝔼 x : G, |normalized B (x+ -t)-normalized B x|) ≤ δ) :
    |conv (fun x ↦ f x-indicator B x) t-(conv f t-density B)| ≤
      δ*density B*(2*L+1) := by
  have h₁ := cross_indicator_close B hB f hsupp hL hf (-t) hnt
  rw [hmean, ← crossConv_eq_crossCorr f (indicator B) hBeven t] at h₁
  have h₂ := cross_indicator_close B hB (indicator B) (fun x hx ↦ by simp [indicator, hx])
    (by norm_num : (0 : ℝ) ≤ 1) (indicator_abs_le_one B) t ht
  rw [expect_indicator, mul_one] at h₂
  change |corr (indicator B) t-density B| ≤ δ*density B at h₂
  rw [conv_sub_eq, conv_eq_corr_of_even _ hBeven]
  rcases abs_le.mp h₁ with ⟨h₁l,h₁u⟩
  rcases abs_le.mp h₂ with ⟨h₂l,h₂u⟩
  apply abs_le.mpr
  constructor <;> nlinarith

lemma indicator_bohr_even (D : Finset (AddChar G ℂ)) (r : ℝ) (x : G) :
    indicator (bohr D r) (-x) = indicator (bohr D r) x := by
  have he : -x ∈ bohr D r ↔ x ∈ bohr D r := ⟨fun h ↦ by simpa using bohr_neg h, bohr_neg⟩
  simp only [indicator, he]

noncomputable def localNormalized (A B : Finset G) (x : G) : ℝ :=
  indicator A x/relativeDensity A B

lemma relativeDensity_pos (A B : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) :
    0 < relativeDensity A B := by
  unfold relativeDensity
  rw [inter_eq_left.mpr hAB]
  exact div_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast (hA.mono hAB).card_pos)

lemma density_eq_relative_mul (A B : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) :
    density A = relativeDensity A B*density B := by
  unfold density relativeDensity
  rw [inter_eq_left.mpr hAB]
  field_simp [show (B.card : ℝ) ≠ 0 by exact_mod_cast (hA.mono hAB).card_pos.ne']

lemma mean_localNormalized (A B : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) :
    (𝔼 x : G, localNormalized A B x) = density B := by
  unfold localNormalized
  rw [← expect_div, expect_indicator, density_eq_relative_mul A B hA hAB]
  field_simp [(relativeDensity_pos A B hA hAB).ne']

lemma localNormalized_support (A B : Finset G) (hAB : A ⊆ B) (x : G) (hx : x ∉ B) :
    localNormalized A B x = 0 := by
  have hxA : x ∉ A := fun h ↦ hx (hAB h)
  simp [localNormalized, indicator, hxA]

lemma localNormalized_abs_le (A B : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) (x : G) :
    |localNormalized A B x| ≤ 1/relativeDensity A B := by
  rw [localNormalized, abs_div, abs_of_pos (relativeDensity_pos A B hA hAB)]
  exact div_le_div_of_nonneg_right (indicator_abs_le_one A x) (relativeDensity_pos A B hA hAB).le

/-- The two local-centering estimates apply simultaneously on every small shift of a stable Bohr set. -/
theorem bohr_local_centering (D : Finset (AddChar G ℂ)) {r h δ : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A : Finset G) (hA : A.Nonempty) (hAB : A ⊆ bohr D r) {t : G} (ht : t ∈ bohr D h) :
    let B := bohr D r
    let f := localNormalized A B
    (|corr (fun x ↦ f x-indicator B x) t-(corr f t-density B)| ≤
      δ*density B*(2/relativeDensity A B+1)) ∧
    (|conv (fun x ↦ f x-indicator B x) t-(conv f t-density B)| ≤
      δ*density B*(2/relativeDensity A B+1)) := by
  dsimp only
  have hB : (bohr D r).Nonempty := ⟨0,bohr_zero D hr⟩
  have ht' := normalized_bohr_translation_le D hr hh hδ hgrowth ht
  have hnt := normalized_bohr_translation_le D hr hh hδ hgrowth (bohr_neg ht)
  have hL : 0 ≤ 1/relativeDensity A (bohr D r) := (one_div_pos.mpr (relativeDensity_pos A _ hA hAB)).le
  constructor
  · simpa only [mul_one_div] using corr_center_local _ hB (localNormalized A _)
      (localNormalized_support A _ hAB) (mean_localNormalized A _ hA hAB) hL
      (localNormalized_abs_le A _ hA hAB) t ht' hnt
  · simpa only [mul_one_div] using conv_center_local _ hB (indicator_bohr_even D r) (localNormalized A _)
      (localNormalized_support A _ hAB) (mean_localNormalized A _ hA hAB) hL
      (localNormalized_abs_le A _ hA hAB) t ht' hnt

#print axioms corr_center_local
#print axioms conv_center_local
#print axioms bohr_local_centering
end Erdos3LocalCorrelationCentering
