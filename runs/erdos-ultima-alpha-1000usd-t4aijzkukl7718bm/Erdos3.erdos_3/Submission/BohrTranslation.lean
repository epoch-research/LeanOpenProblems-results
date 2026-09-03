import Submission.BohrStableScale
import Submission.PopularAlmostPeriods

/-! Translation stability of normalized Bohr-set averages at a fixed stable scale.
These are local averaging ingredients, not a settlement of the Erdős conjecture. -/
namespace Erdos3BohrTranslation
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrStableScale
  Erdos3CorrelationSifting Erdos3PopularAlmostPeriods Erdos3CorrelationMoments Erdos3CrootSisaskL2
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma indicator_shift_shell (D : Finset (AddChar G ℂ)) {r h : ℝ} (hh : 0 ≤ h)
    {y : G} (hy : y ∈ bohr D h) (x : G) :
    |indicator (bohr D r) (x+y)-indicator (bohr D r) x| ≤
      indicator (bohr D (r+h) \ bohr D (r-h)) x := by
  by_cases hi : x ∈ bohr D (r-h)
  · have hx : x ∈ bohr D r := bohr_mono D (by linarith) hi
    have hxy : x+y ∈ bohr D r := by
      simpa only [sub_add_cancel] using bohr_add hi hy
    simp [indicator, hx, hxy, hi]
  · by_cases ho : x ∈ bohr D (r+h)
    · by_cases hx : x ∈ bohr D r <;> by_cases hxy : x+y ∈ bohr D r <;>
        simp [indicator, hi, ho, hx, hxy]
    · have hx : x ∉ bohr D r := fun hx ↦ ho (bohr_mono D (by linarith) hx)
      have hxy : x+y ∉ bohr D r := by
        intro hxy
        have ht := bohr_add hxy (bohr_neg hy)
        apply ho
        simpa only [add_neg_cancel_right] using ht
      simp [indicator, hi, ho, hx, hxy]

lemma shell_card_le (D : Finset (AddChar G ℂ)) {r h δ : ℝ} (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ)) :
    ((bohr D (r+h) \ bohr D (r-h)).card : ℝ) ≤ δ*((bohr D r).card : ℝ) := by
  have hsub : bohr D (r-h) ⊆ bohr D (r+h) := bohr_mono D (by linarith)
  have hmid : ((bohr D (r-h)).card : ℝ) ≤ (bohr D r).card := by
    exact_mod_cast card_le_card (bohr_mono D (by linarith : r-h ≤ r))
  rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  calc
    _ ≤ δ*((bohr D (r-h)).card : ℝ) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hmid hδ

/-- Normalized uniform measure on a stable Bohr set changes by at most δ in L¹
under translation by any element of the smaller Bohr set. -/
theorem normalized_bohr_translation_le (D : Finset (AddChar G ℂ)) {r h δ : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    {y : G} (hy : y ∈ bohr D h) :
    (𝔼 x : G, |normalized (bohr D r) (x+y)-normalized (bohr D r) x|) ≤ δ := by
  have hB : (bohr D r).Nonempty := ⟨0,bohr_zero D hr⟩
  have hα := density_pos (bohr D r) hB
  have he (x : G) : |normalized (bohr D r) (x+y)-normalized (bohr D r) x| =
      |indicator (bohr D r) (x+y)-indicator (bohr D r) x| / density (bohr D r) := by
    rw [normalized, normalized, ← sub_div, abs_div, abs_of_pos hα]
  simp_rw [he]
  rw [← expect_div]
  apply (div_le_iff₀ hα).mpr
  calc
    _ ≤ 𝔼 x : G, indicator (bohr D (r+h) \ bohr D (r-h)) x :=
      expect_le_expect (fun x _ ↦ indicator_shift_shell D hh hy x)
    _ = density (bohr D (r+h) \ bohr D (r-h)) := expect_indicator _
    _ ≤ δ*density (bohr D r) := by
      unfold density
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (shell_card_le D hh hδ hgrowth) (Nat.cast_nonneg _)

lemma abs_expect_le_expect_abs {V : Type*} [Fintype V] (f : V → ℝ) :
    |𝔼 x, f x| ≤ 𝔼 x, |f x| := by
  simpa only [Real.norm_eq_abs] using RCLike.norm_expect_le (K := ℝ) (f := f) (s := univ)

/-- An L¹ bound for the translation of a weight controls all bounded test functions. -/
lemma weighted_translation_bound (w f : G → ℝ) {M δ : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (y : G) (hw : (𝔼 x : G, |w (x+y)-w x|) ≤ δ) :
    |(𝔼 x : G, w (x+y)*f x)-(𝔼 x : G, w x*f x)| ≤ δ*M := by
  rw [← expect_sub_distrib]
  have he (x : G) : w (x+y)*f x-w x*f x = (w (x+y)-w x)*f x := by ring
  simp_rw [he]
  calc
    _ ≤ 𝔼 x : G, |(w (x+y)-w x)*f x| := abs_expect_le_expect_abs _
    _ ≤ 𝔼 x : G, (|w (x+y)-w x| * M) := by
      apply expect_le_expect
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = (𝔼 x : G, |w (x+y)-w x|) * M := (expect_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hw hM

lemma expect_normalized_mul (B : Finset G) (hB : B.Nonempty) (f : G → ℝ) :
    (𝔼 x : G, normalized B x*f x) = 𝔼 b : B, f b := by
  unfold normalized
  simp_rw [div_mul_eq_mul_div]
  rw [← expect_div, expect_indicator_mul B hB]
  field_simp [(density_pos B hB).ne']

lemma smooth_weighted (B : Finset G) (hB : B.Nonempty) (f : G → ℝ) (y : G) :
    smooth B f y = 𝔼 x : G, normalized B (x-y)*f x := by
  calc
    _ = 𝔼 x : G, normalized B x*f (x+y) := by
      rw [expect_normalized_mul B hB]
      apply expect_congr rfl
      intro b _
      simp only [add_comm]
    _ = _ := Fintype.expect_equiv (Equiv.addRight y) _ _ (fun x ↦ by simp)

/-- Bounded functions averaged on a stable Bohr set have uniformly close nearby translates. -/
theorem smooth_bohr_translation_le (D : Finset (AddChar G ℂ)) {r h δ M : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ M) {y : G} (hy : y ∈ bohr D h) (z : G) :
    |smooth (bohr D r) f (z+y)-smooth (bohr D r) f z| ≤ δ*M := by
  let g : G → ℝ := fun x ↦ f (z+x)
  have hB : (bohr D r).Nonempty := ⟨0,bohr_zero D hr⟩
  have ht := weighted_translation_bound (normalized (bohr D r)) g hM
    (fun x ↦ hf (z+x)) (-y) (normalized_bohr_translation_le D hr hh hδ hgrowth (bohr_neg hy))
  have he : (𝔼 x : G, normalized (bohr D r) (x+ -y)*g x) = smooth (bohr D r) g y := by
    simpa only [sub_eq_add_neg] using (smooth_weighted (bohr D r) hB g y).symm
  have he0 : (𝔼 x : G, normalized (bohr D r) x*g x) = smooth (bohr D r) g 0 := by
    simpa only [sub_zero] using (smooth_weighted (bohr D r) hB g 0).symm
  rw [he, he0] at ht
  simpa only [smooth, g, zero_add, add_assoc] using ht

/-- Stable scales with an explicit translation window exist at every positive radius. -/
theorem exists_translation_stable_bohr (D : Finset (AddChar G ℂ)) {R : ℝ} (hR : 0 < R)
    {q : ℕ} (hq : 0 < q) :
    ∃ r : ℝ, R ≤ r-stabilityWidth D q R ∧ r+stabilityWidth D q R ≤ 2*R ∧
      ∀ y ∈ bohr D (stabilityWidth D q R),
        (𝔼 x : G, |normalized (bohr D r) (x+y)-normalized (bohr D r) x|) ≤ 1/(q : ℝ) := by
  obtain ⟨r,hr₁,hr₂,hgrowth⟩ := exists_stable_radius D hR hq
  have hw := stabilityWidth_pos D hq hR
  refine ⟨r,hr₁,hr₂,?_⟩
  intro y hy
  exact normalized_bohr_translation_le D (by linarith) hw.le (by positivity) hgrowth hy

#print axioms normalized_bohr_translation_le
#print axioms smooth_bohr_translation_le
#print axioms exists_translation_stable_bohr
end Erdos3BohrTranslation
