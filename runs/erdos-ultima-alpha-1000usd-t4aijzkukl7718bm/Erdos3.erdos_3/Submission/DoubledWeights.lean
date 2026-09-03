import Submission.LocalThreeAPMoment

/-! Transport of normalized correlations under additive equivalences, and a doubled-center
weight identity for groups in which doubling is bijective. Auxiliary results only. -/
namespace Erdos3DoubledWeights
open Finset Erdos3CorrelationSifting Erdos3CorrelationMoments Erdos3PopularAlmostPeriods
  Erdos3BohrTranslation Erdos3BohrLocalAverages Erdos3LocalThreeAPMoment
  Erdos3FiniteBohr Erdos3LocalCorrelationCentering Erdos3CrootSisaskL2
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 2000000

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]

lemma density_image (e : G ≃+ H) (C : Finset G) : density (C.image e) = density C := by
  unfold density
  rw [card_image_of_injective _ e.injective, Fintype.card_congr e.toEquiv]

lemma normalized_image (e : G ≃+ H) (C : Finset G) (x : G) :
    normalized (C.image e) (e x) = normalized C x := by
  simp only [normalized, density_image, indicator, mem_image, e.injective.eq_iff, exists_eq_right]

lemma corr_normalized_image (e : G ≃+ H) (C : Finset G) (t : G) :
    corr (normalized (C.image e)) (e t) = corr (normalized C) t := by
  unfold corr
  symm
  exact Fintype.expect_equiv e.toEquiv _ _ (fun x ↦ by
    change normalized C x * normalized C (x+t) =
      normalized (C.image e) (e x) * normalized (C.image e) (e x+e t)
    rw [← e.map_add, normalized_image, normalized_image])

variable (G) in
noncomputable def doublingEquiv (h2 : Function.Bijective (fun x : G ↦ x+x)) : G ≃+ G :=
  AddEquiv.ofBijective
    ({ toFun := fun x ↦ x+x
       map_zero' := by simp
       map_add' := fun x y ↦ by abel } : G →+ G) h2

lemma doublingEquiv_apply (h2 : Function.Bijective (fun x : G ↦ x+x)) (x : G) :
    doublingEquiv G h2 x = x+x := rfl

lemma corr_pairing (g f : G → ℝ) (x : G) :
    (𝔼 t : G, corr g t*f (x+t)) =
      𝔼 b : G, g b*(𝔼 c : G, g c*f (x+c-b)) := by
  unfold corr
  simp_rw [expect_mul]
  rw [expect_comm]
  apply expect_congr rfl
  intro b _
  rw [mul_expect]
  exact Fintype.expect_equiv (Equiv.addRight b) _ _ (fun t ↦ by
    change g b * g (b+t) * f (x+t) = g b * (g (t+b) * f (x+(t+b)-b))
    have he : x+(t+b)-b = x+t := by abel
    rw [he, add_comm b t]
    ring)

lemma normalized_corr_pairing (C : Finset G) (hC : C.Nonempty) (f : G → ℝ) (x : G) :
    (𝔼 t : G, corr (normalized C) t*f (x+t)) = diffSmooth C f x := by
  rw [corr_pairing, expect_normalized_mul C hC]
  simp_rw [expect_normalized_mul C hC]
  rfl

/-- Doubling the averaging set turns mass at doubled centers into an ordinary symmetric average. -/
theorem doubled_mass_eq_diffSmooth (h2 : Function.Bijective (fun x : G ↦ x+x))
    (C Z : Finset G) (hC : C.Nonempty) :
    doubledMass Z (corr (normalized (C.image (doublingEquiv G h2)))) =
      diffSmooth C (indicator Z) 0 := by
  calc
    _ = 𝔼 t : G, corr (normalized C) t*indicator Z t := by
      unfold doubledMass
      have ht (t : G) : corr (normalized (C.image (doublingEquiv G h2))) (t+t) =
          corr (normalized C) t := corr_normalized_image (doublingEquiv G h2) C t
      simp_rw [ht]
      rw [Fintype.expect_eq_sum_div_card]
      simp [indicator, mul_ite, sum_filter]
    _ = _ := by simpa only [zero_add] using normalized_corr_pairing C hC (indicator Z) 0

noncomputable def window (A U : Finset G) (x : G) : Finset G := U.filter (fun a ↦ x+a ∈ A)

lemma window_subset (A U : Finset G) (x : G) : window A U x ⊆ U := filter_subset _ _

lemma window_mono (A : Finset G) {U V : Finset G} (hUV : U ⊆ V) (x : G) :
    window A U x ⊆ window A V x := by
  intro a ha
  exact mem_filter.mpr ⟨hUV (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩

lemma relativeDensity_window (A U : Finset G) (x : G) :
    relativeDensity (window A U x) U = smooth U (indicator A) x := by
  rw [← mean_indicator_eq_relativeDensity]
  apply expect_congr rfl
  intro u _
  simp [indicator, window, u.property]

lemma window_threeAPFree (A U : Finset G) (hA : ThreeAPFree (A : Set G)) (x : G) :
    ThreeAPFree (window A U x : Set G) := by
  intro a ha b hb c hc he
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  have hc' := (mem_filter.mp hc).2
  have hsum : (x+a)+(x+c) = (x+b)+(x+b) := by
    calc
      _ = (x+x)+(a+c) := by abel
      _ = (x+x)+(b+b) := congrArg (fun y ↦ (x+x)+y) he
      _ = _ := by abel
  exact add_left_cancel (hA ha' hb' hc' hsum)

lemma diffSmooth_window (A U C : Finset G) (x : G)
    (hsub : ∀ b ∈ C, ∀ c ∈ C, c-b ∈ U) :
    diffSmooth C (indicator (window A U x)) 0 = diffSmooth C (indicator A) x := by
  unfold diffSmooth
  apply expect_congr rfl
  intro b _
  apply expect_congr rfl
  intro c _
  have hm := hsub b b.property c c.property
  simp only [zero_add, indicator, window, mem_filter, hm, true_and, add_sub_assoc]

lemma corr_normalized_nonzero (C : Finset G) {t : G} (ht : corr (normalized C) t ≠ 0) :
    ∃ b ∈ C, ∃ c ∈ C, t = c-b := by
  by_contra! h
  apply ht
  apply expect_eq_zero
  intro b _
  by_cases hb : b ∈ C
  · have hc : b+t ∉ C := by
      intro hc
      exact h b hb (b+t) hc (by abel)
    simp [normalized, indicator, hc]
  · simp [normalized, indicator, hb]

lemma normalized_nonneg (C : Finset G) (x : G) : 0 ≤ normalized C x :=
  div_nonneg (indicator_nonneg C x) (density_nonneg C)

lemma normalized_even (C : Finset G) (hC : ∀ x ∈ C, -x ∈ C) (x : G) :
    normalized C (-x) = normalized C x := by
  have he : -x ∈ C ↔ x ∈ C := ⟨fun hx ↦ by simpa using hC (-x) hx, hC x⟩
  simp only [normalized, indicator, he]

lemma normalized_image_even (e : G ≃+ H) (C : Finset G)
    (hC : ∀ x ∈ C, -x ∈ C) (y : H) :
    normalized (C.image e) (-y) = normalized (C.image e) y := by
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [← e.map_neg, normalized_image, normalized_image]
  exact normalized_even C hC x

lemma doubled_weight_support (h2 : Function.Bijective (fun x : G ↦ x+x))
    (D : Finset (AddChar G ℂ)) {ρ : ℝ} (C : Finset G) (hC : C ⊆ bohr D ρ)
    {t : G} (ht : corr (normalized (C.image (doublingEquiv G h2))) t ≠ 0) :
    t ∈ bohr D (4*ρ) := by
  obtain ⟨b₀,hb₀,c₀,hc₀,rfl⟩ := corr_normalized_nonzero _ ht
  obtain ⟨b,hb,hbeq⟩ := mem_image.mp hb₀
  obtain ⟨c,hc,hceq⟩ := mem_image.mp hc₀
  subst b₀
  subst c₀
  have hb' := bohr_add (hC hb) (hC hb)
  have hc' := bohr_add (hC hc) (hC hc)
  have h := bohr_add hc' (bohr_neg hb')
  have he : (ρ+ρ)+(ρ+ρ) = 4*ρ := by ring
  simpa only [doublingEquiv_apply, sub_eq_add_neg, he] using h

/-- Localized doubled mass is exactly a shifted symmetric average when the window
contains all pair differences of C. -/
theorem doubled_mass_window (h2 : Function.Bijective (fun x : G ↦ x+x))
    (A U C : Finset G) (hC : C.Nonempty) (x : G)
    (hsub : ∀ b ∈ C, ∀ c ∈ C, c-b ∈ U) :
    doubledMass (window A U x) (corr (normalized (C.image (doublingEquiv G h2)))) =
      diffSmooth C (indicator A) x := by
  rw [doubled_mass_eq_diffSmooth h2 C _ hC, diffSmooth_window A U C x hsub]

#print axioms doubled_mass_eq_diffSmooth
#print axioms doubled_weight_support
#print axioms doubled_mass_window
end Erdos3DoubledWeights
