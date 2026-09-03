import Submission.BohrTranslation

/-! Stable local averages and dense translated windows inside finite Bohr sets.
These are auxiliary localization lemmas, not the original conjecture. -/
namespace Erdos3BohrLocalAverages
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrStableScale Erdos3BohrTranslation
  Erdos3CorrelationSifting Erdos3CrootSisaskL2
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma abs_pairing_le (g h f : G → ℝ) {δ M : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M)
    (hgh : (𝔼 x : G, |g x-h x|) ≤ δ) :
    |(𝔼 x : G, g x*f x)-(𝔼 x : G, h x*f x)| ≤ δ*M := by
  rw [← expect_sub_distrib]
  have he (x : G) : g x*f x-h x*f x = (g x-h x)*f x := by ring
  simp_rw [he]
  calc
    _ ≤ 𝔼 x : G, |(g x-h x)*f x| := abs_expect_le_expect_abs _
    _ ≤ 𝔼 x : G, (|g x-h x| * M) := by
      apply expect_le_expect
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = (𝔼 x : G, |g x-h x|)*M := (expect_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hgh hM

lemma mean_abs_smooth_sub_le (W : Finset G) (hW : W.Nonempty) (g : G → ℝ) {δ : ℝ}
    (htrans : ∀ y ∈ W, (𝔼 x : G, |g (x+y)-g x|) ≤ δ) :
    (𝔼 x : G, |smooth W g x-g x|) ≤ δ := by
  letI : Nonempty W := hW.to_subtype
  have he (x : G) : smooth W g x-g x = 𝔼 w : W, (g (x+(w : G))-g x) := by
    simp only [smooth, expect_sub_distrib, Fintype.expect_const]
  simp_rw [he]
  calc
    _ ≤ 𝔼 x : G, 𝔼 w : W, |g (x+(w : G))-g x| :=
      expect_le_expect (fun x _ ↦ abs_expect_le_expect_abs _)
    _ = 𝔼 w : W, 𝔼 x : G, |g (x+(w : G))-g x| := expect_comm _ _ _
    _ ≤ _ := expect_le univ_nonempty (fun w _ ↦ htrans w w.property)

/-- Averaging a normalized stable Bohr measure over smaller shifts is an approximate identity. -/
theorem normalized_bohr_absorption (D : Finset (AddChar G ℂ)) {r h δ : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (W : Finset G) (hW : W.Nonempty) (hsub : W ⊆ bohr D h) :
    (𝔼 x : G, |smooth W (normalized (bohr D r)) x-normalized (bohr D r) x|) ≤ δ :=
  mean_abs_smooth_sub_le W hW _ (fun y hy ↦ normalized_bohr_translation_le D hr hh hδ hgrowth (hsub hy))

lemma mean_smooth_exchange (B W : Finset G) (f : G → ℝ) :
    (𝔼 b : B, smooth W f b) = 𝔼 w : W, smooth B f w := by
  unfold smooth
  rw [expect_comm]
  apply expect_congr rfl
  intro w _
  apply expect_congr rfl
  intro b _
  simp only [add_comm]

/-- A stable local average changes little when it is smoothed over a smaller set. -/
theorem mean_bohr_smooth_close (D : Finset (AddChar G ℂ)) {r h δ M : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (W : Finset G) (hW : W.Nonempty) (hsub : W ⊆ bohr D h)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ M) :
    |(𝔼 b : bohr D r, smooth W f b)-(𝔼 b : bohr D r, f b)| ≤ δ*M := by
  letI : Nonempty W := hW.to_subtype
  rw [mean_smooth_exchange]
  have hz : (𝔼 b : bohr D r, f b) = smooth (bohr D r) f 0 := by simp only [smooth, zero_add]
  rw [hz, ← Fintype.expect_const (ι := W) (smooth (bohr D r) f 0), ← expect_sub_distrib]
  apply (abs_expect_le_expect_abs _).trans
  apply expect_le univ_nonempty
  intro w _
  simpa only [zero_add] using smooth_bohr_translation_le D hr hh hδ hM hgrowth f hf (hsub w.property) 0

noncomputable def relativeDensity (A B : Finset G) : ℝ := (A ∩ B).card / (B.card : ℝ)

lemma mean_indicator_eq_relativeDensity (A B : Finset G) :
    (𝔼 b : B, indicator A b) = relativeDensity A B := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_coe, sum_coe_sort]
  simp [indicator, relativeDensity, filter_mem_eq_inter, inter_comm]

lemma indicator_abs_le_one (A : Finset G) (x : G) : |indicator A x| ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

/-- A stable Bohr set contains the center of a small translated window retaining
its relative density, up to the chosen additive tolerance. -/
theorem exists_dense_window (D : Finset (AddChar G ℂ)) {r h δ : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A W : Finset G) (hW : W.Nonempty) (hsub : W ⊆ bohr D h) :
    ∃ b ∈ bohr D r,
      relativeDensity A (bohr D r)-δ ≤ smooth W (indicator A) b ∧
      W.image (fun w ↦ b+w) ⊆ bohr D (r+h) := by
  let B := bohr D r
  have hB : B.Nonempty := ⟨0,bohr_zero D hr⟩
  letI : Nonempty B := hB.to_subtype
  have havg := mean_bohr_smooth_close D hr hh hδ (by norm_num : (0 : ℝ) ≤ 1)
    hgrowth W hW hsub (indicator A) (indicator_abs_le_one A)
  rw [mean_indicator_eq_relativeDensity, mul_one] at havg
  obtain ⟨b,_,hb⟩ := exists_max_image (univ : Finset B) (fun b ↦ smooth W (indicator A) b) univ_nonempty
  have hmax : (𝔼 x : B, smooth W (indicator A) x) ≤ smooth W (indicator A) b :=
    expect_le univ_nonempty hb
  refine ⟨b,b.property,?_,?_⟩
  · have hl := (abs_le.mp havg).1
    change (𝔼 x : bohr D r, smooth W (indicator A) x) ≤ smooth W (indicator A) b at hmax
    linarith
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hx
    exact bohr_add b.property (hsub hw)

#print axioms normalized_bohr_absorption
#print axioms mean_bohr_smooth_close
#print axioms exists_dense_window
end Erdos3BohrLocalAverages
