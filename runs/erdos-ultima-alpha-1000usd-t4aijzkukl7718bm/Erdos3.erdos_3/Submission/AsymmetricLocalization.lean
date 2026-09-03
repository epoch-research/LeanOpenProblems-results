import Submission.AsymmetricSifting

/-! Stable averaging localizes a symmetric moment to an asymmetric pair of windows.
This supplies the input for asymmetric sifting. Auxiliary results only. -/
namespace Erdos3AsymmetricLocalization
open Finset Erdos3AsymmetricSifting Erdos3CorrelationSifting Erdos3CorrelationMoments
  Erdos3LocalCorrelationCentering Erdos3LocalCorrelationSifting Erdos3BohrLocalAverages
  Erdos3BohrTranslation Erdos3FiniteBohr Erdos3BohrCovering Erdos3CrootSisaskL2
open scoped BigOperators Classical
set_option maxHeartbeats 2500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def shiftSet (U : Finset G) (x : G) : Finset G := U.image (fun u ↦ x+u)

lemma shiftSet_nonempty (U : Finset G) (hU : U.Nonempty) (x : G) :
    (shiftSet U x).Nonempty := hU.image _

lemma shiftSet_card (U : Finset G) (x : G) : (shiftSet U x).card = U.card :=
  card_image_of_injective _ (fun _ _ h ↦ add_left_cancel h)

lemma shiftSet_density (U : Finset G) (x : G) : density (shiftSet U x) = density U := by
  simp only [density, shiftSet_card]

lemma expect_shiftSet (U : Finset G) (x : G) (f : G → ℝ) :
    (𝔼 y : shiftSet U x, f y) = 𝔼 u : U, f (x+(u : G)) := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_coe, sum_coe_sort, shiftSet_card]
  unfold shiftSet
  rw [sum_image (fun a _ b _ h ↦ add_left_cancel h), sum_coe_sort U (fun u : G ↦ f (x+u))]

lemma crossAverage_shiftSet (C U : Finset G) (x : G) (f : G → ℝ) :
    crossAverage C (shiftSet U x) f = smooth U (fun y ↦ 𝔼 c : C, f (y-(c : G))) x := by
  unfold crossAverage
  calc
    _ = 𝔼 c : C, 𝔼 u : U, f (x+(u : G)-(c : G)) := by
      apply expect_congr rfl
      intro c _
      exact expect_shiftSet U x (fun y : G ↦ f (y-(c : G)))
    _ = _ := expect_comm _ _ _

lemma crossAverage_self (C : Finset G) (hC : C.Nonempty) (f : G → ℝ) :
    crossAverage C C f = 𝔼 t : G, corr (normalized C) t*f t :=
  crossAverage_eq_pairing C C hC hC f

/-- A large symmetric average survives localization of its second argument to a
translate of a much smaller set, with only the stability error. -/
theorem exists_localized_crossAverage (D : Finset (AddChar G ℂ)) {r h δ M : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (U : Finset G) (hU : U.Nonempty) (hUsub : U ⊆ bohr D h)
    (f : G → ℝ) (hf : ∀ t, |f t| ≤ M) :
    ∃ x ∈ bohr D r,
      crossAverage (bohr D r) (bohr D r) f-δ*M ≤
        crossAverage (bohr D r) (shiftSet U x) f := by
  let C := bohr D r
  have hC : C.Nonempty := ⟨0,bohr_zero D hr⟩
  letI : Nonempty C := hC.to_subtype
  let g : G → ℝ := fun y ↦ 𝔼 c : C, f (y-(c : G))
  have hg (y : G) : |g y| ≤ M := by
    apply (abs_expect_le_expect_abs _).trans
    exact expect_le univ_nonempty (fun c _ ↦ hf _)
  have hmean := mean_bohr_smooth_close D hr hh hδ hM hgrowth U hU hUsub g hg
  have he : (𝔼 c : C, g c) = crossAverage C C f := expect_comm _ _ _
  change |(𝔼 c : C, smooth U g c)-(𝔼 c : C, g c)| ≤ δ*M at hmean
  rw [he] at hmean
  obtain ⟨x,_,hx⟩ := exists_max_image (univ : Finset C) (fun c ↦ smooth U g c) univ_nonempty
  have hmax : (𝔼 c : C, smooth U g c) ≤ smooth U g x := expect_le univ_nonempty hx
  refine ⟨x,x.property,?_⟩
  rw [crossAverage_shiftSet]
  change crossAverage C C f-δ*M ≤ smooth U g x
  linarith [(abs_le.mp hmean).1]

lemma corr_indicator_le_density (A : Finset G) (t : G) : corr (indicator A) t ≤ density A := by
  rw [← expect_indicator A]
  unfold corr
  apply expect_le_expect
  intro x _
  have h1 : indicator A (x+t) ≤ 1 := (le_abs_self _).trans (indicator_abs_le_one A _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 (indicator_nonneg A x)

lemma local_correlation_bound (A B : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) (t : G) :
    0 ≤ corr (localNormalized A B) t/density B ∧
      corr (localNormalized A B) t/density B ≤ 1/relativeDensity A B := by
  have hα := relativeDensity_pos A B hA hAB
  have hβ := density_pos B (hA.mono hAB)
  rw [corr_localNormalized, div_div]
  constructor
  · exact div_nonneg (corr_indicator_nonneg A t) (by positivity)
  · calc
      _ ≤ density A/((relativeDensity A B)^2*density B) :=
        div_le_div_of_nonneg_right (corr_indicator_le_density A t) (by positivity)
      _ = _ := by
        rw [density_eq_relative_mul A B hA hAB]
        field_simp

lemma local_correlation_power_bound (A B : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B)
    (p : ℕ) (t : G) :
    |(corr (localNormalized A B) t/density B)^p| ≤ (1/relativeDensity A B)^p := by
  obtain ⟨hn,hb⟩ := local_correlation_bound A B hA hAB t
  rw [abs_of_nonneg (pow_nonneg hn _)]
  exact pow_le_pow_left₀ hn hb p

/-- Localize a high correlation moment without introducing the ratio |C|/|U|. -/
theorem exists_asymmetric_moment (D : Finset (AddChar G ℂ)) {r h δ H K : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A B U : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) (hU : U.Nonempty)
    (hUsub : U ⊆ bohr D h) (p : ℕ)
    (hmoment : H^p ≤ 𝔼 t : G, corr (normalized (bohr D r)) t*
      (corr (localNormalized A B) t/density B)^p)
    (herror : δ*(1/relativeDensity A B)^p ≤ H^p-K^p) :
    ∃ x ∈ bohr D r,
      K^p ≤ 𝔼 t : G, crossCorr (normalized (bohr D r)) (normalized (shiftSet U x)) t*
        (corr (localNormalized A B) t/density B)^p := by
  have hα := relativeDensity_pos A B hA hAB
  let f : G → ℝ := fun t ↦ (corr (localNormalized A B) t/density B)^p
  have hC : (bohr D r).Nonempty := ⟨0,bohr_zero D hr⟩
  obtain ⟨x,hx,havg⟩ := exists_localized_crossAverage D hr hh hδ
    (by positivity : 0 ≤ (1/relativeDensity A B)^p) hgrowth U hU hUsub f
    (local_correlation_power_bound A B hA hAB p)
  rw [crossAverage_self _ hC, crossAverage_eq_pairing _ _ hC (shiftSet_nonempty U hU x)] at havg
  refine ⟨x,hx,?_⟩
  change (𝔼 t : G, corr (normalized (bohr D r)) t*
      (corr (localNormalized A B) t/density B)^p) - δ*(1/relativeDensity A B)^p ≤
    (𝔼 t : G, crossCorr (normalized (bohr D r)) (normalized (shiftSet U x)) t*
      (corr (localNormalized A B) t/density B)^p) at havg
  linarith

/-- Stable moment localization followed by asymmetric DRC. Both relative densities
are bounded independently of the ambient densities of the two windows. -/
theorem localize_and_sift (D : Finset (AddChar G ℂ)) {r h δ L H K : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hL : 0 < L) (hK : 0 < K)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A B U V : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B) (hU : U.Nonempty)
    (hUsub : U ⊆ bohr D h) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ bohr D r, a-c ∈ V)
    (hVsize : density V ≤ K*density B) (p : ℕ)
    (hmoment : H^p ≤ 𝔼 t : G, corr (normalized (bohr D r)) t*
      (corr (localNormalized A B) t/density B)^p)
    (herror : δ*(1/relativeDensity A B)^p ≤ H^p-K^p) :
    ∃ x ∈ bohr D r, ∃ S ⊆ bohr D r, ∃ T ⊆ shiftSet U x,
      S.Nonempty ∧ T.Nonempty ∧
      (relativeDensity A B)^(2*p) ≤ 2*relativeDensity S (bohr D r) ∧
      (relativeDensity A B)^(2*p) ≤ 2*relativeDensity T (shiftSet U x) ∧
      crossPairDensity S T (fun t ↦ if corr (localNormalized A B) t/density B ≤ L then 1 else 0) ≤
        2*(L/K)^p*density S*density T := by
  obtain ⟨x,hx,hm⟩ := exists_asymmetric_moment D hr hh hδ hgrowth A B U hA hAB hU hUsub p hmoment herror
  refine ⟨x,hx,?_⟩
  exact exists_relative_asymmetric_sets A B (bohr D r) (shiftSet U x) V hA hAB
    ⟨0,bohr_zero D hr⟩ (shiftSet_nonempty U hU x) hV hsupport p hL hK hVsize hm

/-- The cross-differences lie in one translate of a small enlargement, not in 2C. -/
lemma cross_differences_in_enlargement (D : Finset (AddChar G ℂ)) {r h : ℝ}
    (U S T : Finset G) (x : G) (hU : U ⊆ bohr D h) (hS : S ⊆ bohr D r)
    (hT : T ⊆ shiftSet U x) :
    ∀ s ∈ S, ∀ t ∈ T, t-s ∈ shiftSet (bohr D (r+h)) x := by
  intro s hs t ht
  obtain ⟨u,hu,rfl⟩ := mem_image.mp (hT ht)
  apply mem_image.mpr
  refine ⟨u-s,?_,by abel⟩
  have he := bohr_add (bohr_neg (hS hs)) (hU hu)
  simpa only [sub_eq_add_neg, add_comm] using he

lemma crossPairDensity_truncate (S T W : Finset G) (f : G → ℝ)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W) :
    crossPairDensity S T (fun t ↦ indicator W t*f t) = crossPairDensity S T f := by
  unfold crossPairDensity
  apply expect_congr rfl
  intro s _
  apply expect_congr rfl
  intro t _
  by_cases hs : s ∈ S
  · by_cases ht : t ∈ T
    · simp [indicator, hs, ht, hW s hs t ht]
    · simp [indicator, ht]
  · simp [indicator, hs]

#print axioms exists_localized_crossAverage
#print axioms exists_asymmetric_moment
#print axioms localize_and_sift
#print axioms cross_differences_in_enlargement
end Erdos3AsymmetricLocalization
