import Submission.PopularBohr

/-! A global density-increment criterion from popular correlations on a Bohr set.
The localized iteration and the original Erdős conjecture are not proved here. -/
namespace Erdos3CorrelationIncrement
open Finset Erdos3CorrelationSifting Erdos3PopularAlmostPeriods Erdos3CorrelationMoments
  Erdos3CrootSisaskL2 Erdos3FiniteBohr
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma smooth_comm (B V : Finset G) (g : G → ℝ) (x : G) :
    smooth B (smooth V g) x = smooth V (smooth B g) x := by
  unfold smooth
  rw [expect_comm]
  apply expect_congr rfl
  intro v _
  apply expect_congr rfl
  intro b _
  congr 1
  abel

lemma mean_smooth (B : Finset G) (hB : B.Nonempty) (g : G → ℝ) :
    (𝔼 x : G, smooth B g x) = 𝔼 x : G, g x := by
  letI : Nonempty B := hB.to_subtype
  unfold smooth
  rw [expect_comm]
  simp_rw [expect_translate]
  exact Fintype.expect_const _

lemma smooth_nonneg (B : Finset G) (g : G → ℝ) (hg : ∀ x, 0 ≤ g x) (x : G) :
    0 ≤ smooth B g x := expect_nonneg (fun _ _ ↦ hg _)

lemma corr_smooth (B : Finset G) (g : G → ℝ) (x : G) :
    corr (smooth B g) x = diffSmooth B (corr g) x := by
  unfold corr smooth diffSmooth
  simp_rw [Fintype.expect_mul_expect]
  calc
    _ = 𝔼 b : B, 𝔼 c : B, 𝔼 y : G, g (y+(b : G))*g (y+x+(c : G)) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro b _
      exact expect_comm _ _ _
    _ = _ := by
      apply expect_congr rfl
      intro b _
      apply expect_congr rfl
      intro c _
      change (𝔼 y : G, g (y+(b : G))*g (y+x+(c : G))) = corr g (x+(c : G)-(b : G))
      rw [corr_gram]
      apply expect_congr rfl
      intro y _
      congr 2 <;> abel

lemma corr_zero (g : G → ℝ) : corr g 0 = 𝔼 x : G, (g x)^2 := by
  simp only [corr, add_zero, sq]

lemma diffSmooth_mono (B : Finset G) (f g : G → ℝ) (h : ∀ x, f x ≤ g x) (x : G) :
    diffSmooth B f x ≤ diffSmooth B g x :=
  expect_le_expect (fun _ _ ↦ expect_le_expect (fun _ _ ↦ h _))

lemma diffSmooth_const_mul (B : Finset G) (g : G → ℝ) (a : ℝ) (x : G) :
    diffSmooth B (fun y ↦ a*g y) x = a*diffSmooth B g x := by
  simp only [diffSmooth, ← mul_expect]

/-- High correlation averaged over B at every difference of V forces increased
mean density on some translate of V. -/
theorem exists_translate_increment (B V : Finset G) (hB : B.Nonempty) (hV : V.Nonempty)
    (g : G → ℝ) (hg : ∀ x, 0 ≤ g x) (hmean : (𝔼 x : G, g x) = 1) {C : ℝ}
    (hc : ∀ s ∈ V, ∀ t ∈ V, C ≤ diffSmooth B (corr g) (s-t)) :
    ∃ x : G, C ≤ smooth V g x := by
  letI : Nonempty B := hB.to_subtype
  letI : Nonempty V := hV.to_subtype
  obtain ⟨x,_,hx⟩ := exists_max_image (univ : Finset G) (smooth V g) univ_nonempty
  let h : G → ℝ := smooth V (smooth B g)
  have hnon (y : G) : 0 ≤ h y := smooth_nonneg V _ (smooth_nonneg B g hg) y
  have hup (y : G) : h y ≤ smooth V g x := by
    dsimp only [h]
    rw [← smooth_comm]
    exact expect_le univ_nonempty (fun b _ ↦ hx _ (mem_univ _))
  have hmean' : (𝔼 y : G, h y) = 1 := by
    dsimp only [h]
    rw [mean_smooth V hV, mean_smooth B hB, hmean]
  have hsq : (𝔼 y : G, (h y)^2) ≤ smooth V g x := by
    calc
      _ ≤ 𝔼 y : G, smooth V g x*h y := expect_le_expect
        (fun y _ ↦ by simpa only [sq] using mul_le_mul_of_nonneg_right (hup y) (hnon y))
      _ = _ := by rw [← mul_expect, hmean', mul_one]
  have hlow : C ≤ 𝔼 y : G, (h y)^2 := by
    rw [← corr_zero]
    dsimp only [h]
    rw [corr_smooth V]
    unfold diffSmooth
    apply le_expect univ_nonempty
    intro v _
    apply le_expect univ_nonempty
    intro w _
    simpa only [corr_smooth, zero_add] using hc w w.property v v.property
  exact ⟨x, hlow.trans hsq⟩

/-- Concentration on a Bohr set of shifts gives a density increment on the Bohr set of half radius. -/
theorem bohr_translate_increment (B : Finset G) (hB : B.Nonempty)
    (D : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (g f : G → ℝ) (hg : ∀ x, 0 ≤ g x) (hmean : (𝔼 x : G, g x) = 1)
    {H c : ℝ} (hH : 0 ≤ H) (hfc : ∀ x, H*f x ≤ corr g x)
    (hpop : ∀ t ∈ bohr D ρ, c ≤ diffSmooth B f t) :
    ∃ x : G, H*c ≤ smooth (bohr D (ρ/2)) g x := by
  have hV : (bohr D (ρ/2)).Nonempty := ⟨0, bohr_zero D (by positivity)⟩
  apply exists_translate_increment B (bohr D (ρ/2)) hB hV g hg hmean
  intro s hs t ht
  have hst : s-t ∈ bohr D ρ := by
    have h := bohr_add hs (bohr_neg ht)
    simpa only [← sub_eq_add_neg, add_halves] using h
  calc
    H*c ≤ H*diffSmooth B f (s-t) := mul_le_mul_of_nonneg_left (hpop _ hst) hH
    _ = diffSmooth B (fun y ↦ H*f y) (s-t) := (diffSmooth_const_mul ..).symm
    _ ≤ _ := diffSmooth_mono B _ _ hfc _

lemma popular_indicator_bound (g : G → ℝ) (hg : ∀ x, 0 ≤ g x) (H : ℝ) (x : G) :
    H*(if H < corr g x then 1 else 0) ≤ corr g x := by
  by_cases hx : H < corr g x
  · simpa only [if_pos hx, mul_one] using hx.le
  · simp only [if_neg hx, mul_zero]
    exact expect_nonneg (fun _ _ ↦ mul_nonneg (hg _) (hg _))

#print axioms corr_smooth
#print axioms exists_translate_increment
#print axioms bohr_translate_increment
end Erdos3CorrelationIncrement
