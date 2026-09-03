import Submission.AsymmetricFourierSmoothing
import Submission.CorrelationIncrement

/-! A density increment criterion for asymmetric popular differences. The increment
window itself, rather than its difference set, is sufficient. Auxiliary results only. -/
namespace Erdos3AsymmetricIncrement
open Finset Erdos3AsymmetricSifting Erdos3AsymmetricFourierSmoothing Erdos3CorrelationSifting
  Erdos3CorrelationMoments Erdos3LocalCorrelationCentering Erdos3BohrLocalAverages
  Erdos3CrootSisaskL2 Erdos3CorrelationIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma crossCorr_smooth (S T : Finset G) (g : G → ℝ) (y : G) :
    crossCorr (smooth S g) (smooth T g) y = crossSmooth S T (corr g) y := by
  unfold crossCorr smooth crossSmooth
  simp_rw [Fintype.expect_mul_expect]
  calc
    _ = 𝔼 s : S, 𝔼 t : T, 𝔼 x : G,
        g (x+(s : G))*g (x+y+(t : G)) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro s _
      exact expect_comm _ _ _
    _ = _ := by
      apply expect_congr rfl
      intro s _
      apply expect_congr rfl
      intro t _
      rw [corr_gram]
      apply expect_congr rfl
      intro x _
      congr 2 <;> abel

lemma mean_crossSmooth_corr (S T V : Finset G) (g : G → ℝ) :
    (𝔼 y : V, crossSmooth S T (corr g) y) =
      𝔼 x : G, smooth S g x*smooth T (smooth V g) x := by
  simp_rw [← crossCorr_smooth]
  unfold crossCorr
  rw [expect_comm]
  apply expect_congr rfl
  intro x _
  rw [← mul_expect, smooth_comm]
  rfl

/-- A high averaged cross-correlation forces a high mean on a translate of V. -/
theorem exists_translate_from_crossAverage (S T V : Finset G)
    (hS : S.Nonempty) (hT : T.Nonempty) (hV : V.Nonempty)
    (g : G → ℝ) (hg : ∀ x, 0 ≤ g x) {μ c : ℝ} (hμ : 0 < μ)
    (hmean : (𝔼 x : G, g x) = μ)
    (hgain : c*μ ≤ 𝔼 y : V, crossSmooth S T (corr g) y) :
    ∃ x : G, c ≤ smooth V g x := by
  letI : Nonempty T := hT.to_subtype
  obtain ⟨x,_,hx⟩ := exists_max_image (univ : Finset G) (smooth V g) univ_nonempty
  have hupper (z : G) : smooth T (smooth V g) z ≤ smooth V g x :=
    expect_le univ_nonempty (fun t _ ↦ hx _ (mem_univ _))
  have hm : (𝔼 z : G, smooth S g z) = μ := by rw [mean_smooth S hS, hmean]
  have hb : (𝔼 y : V, crossSmooth S T (corr g) y) ≤ smooth V g x*μ := by
    rw [mean_crossSmooth_corr]
    calc
      _ ≤ 𝔼 z : G, smooth S g z*smooth V g x :=
        expect_le_expect (fun z _ ↦ mul_le_mul_of_nonneg_left (hupper z) (smooth_nonneg S g hg z))
      _ = _ := by rw [← expect_mul, hm]; ring
  exact ⟨x, by nlinarith [hgain.trans hb]⟩

lemma crossSmooth_mono (S T : Finset G) (f g : G → ℝ) (h : ∀ x, f x ≤ g x) (y : G) :
    crossSmooth S T f y ≤ crossSmooth S T g y :=
  expect_le_expect (fun _ _ ↦ expect_le_expect (fun _ _ ↦ h _))

lemma crossSmooth_const_mul (S T : Finset G) (f : G → ℝ) (c : ℝ) (y : G) :
    crossSmooth S T (fun x ↦ c*f x) y = c*crossSmooth S T f y := by
  simp only [crossSmooth, ← mul_expect]

/-- A popular-difference criterion in local normalization yields an actual increment
of the relative density of A, with no ambient-density factor. -/
theorem local_asymmetric_increment (A B S T V : Finset G)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hS : S.Nonempty) (hT : T.Nonempty) (hV : V.Nonempty)
    (f : G → ℝ) {H c : ℝ} (hH : 0 ≤ H)
    (hfc : ∀ t, H*f t ≤ corr (localNormalized A B) t/density B)
    (hpop : ∀ y ∈ V, c ≤ crossSmooth S T f y) :
    ∃ x : G, H*c*relativeDensity A B ≤ smooth V (indicator A) x := by
  have hα := relativeDensity_pos A B hA hAB
  have hβ := density_pos B (hA.mono hAB)
  letI : Nonempty V := hV.to_subtype
  have hg (x : G) : 0 ≤ localNormalized A B x :=
    div_nonneg (indicator_nonneg A x) hα.le
  have hgain : (H*c)*density B ≤ 𝔼 y : V, crossSmooth S T (corr (localNormalized A B)) y := by
    apply le_expect univ_nonempty
    intro y _
    calc
      _ = (density B*H)*c := by ring
      _ ≤ (density B*H)*crossSmooth S T f y :=
        mul_le_mul_of_nonneg_left (hpop y y.property) (mul_nonneg hβ.le hH)
      _ = crossSmooth S T (fun t ↦ (density B*H)*f t) y := (crossSmooth_const_mul ..).symm
      _ ≤ _ := crossSmooth_mono S T _ _ (fun t ↦ by
        have h := (le_div_iff₀ hβ).mp (hfc t)
        nlinarith) y
  obtain ⟨x,hx⟩ := exists_translate_from_crossAverage S T V hS hT hV (localNormalized A B)
    hg hβ (mean_localNormalized A B hA hAB) hgain
  have he : smooth V (localNormalized A B) x = smooth V (indicator A) x/relativeDensity A B := by
    unfold smooth localNormalized
    exact (expect_div ..).symm
  rw [he] at hx
  exact ⟨x,(le_div_iff₀ hα).mp hx⟩

/-- Specialize the test function to the indicator of popular local correlations. -/
theorem popular_local_asymmetric_increment (A B S T V : Finset G)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hS : S.Nonempty) (hT : T.Nonempty) (hV : V.Nonempty)
    {H c : ℝ} (hH : 0 ≤ H)
    (hpop : ∀ y ∈ V, c ≤ crossSmooth S T
      (fun t ↦ if H < corr (localNormalized A B) t/density B then 1 else 0) y) :
    ∃ x : G, H*c*relativeDensity A B ≤ smooth V (indicator A) x := by
  apply local_asymmetric_increment A B S T V hA hAB hS hT hV _ hH _ hpop
  intro t
  by_cases ht : H < corr (localNormalized A B) t/density B
  · simpa only [if_pos ht, mul_one] using ht.le
  · simp only [if_neg ht, mul_zero]
    exact (Erdos3AsymmetricLocalization.local_correlation_bound A B hA hAB t).1

#print axioms mean_crossSmooth_corr
#print axioms exists_translate_from_crossAverage
#print axioms local_asymmetric_increment
#print axioms popular_local_asymmetric_increment
end Erdos3AsymmetricIncrement
