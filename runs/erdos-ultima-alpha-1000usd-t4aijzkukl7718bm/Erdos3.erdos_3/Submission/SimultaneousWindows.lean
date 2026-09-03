import Submission.DoubledWeights

/-! Simultaneous selection of a dense window and a window with large weighted center mass.
The no-increment assumptions are explicit; this file does not settle Erdős Problem 3. -/
namespace Erdos3SimultaneousWindows
open Finset Erdos3DoubledWeights Erdos3CorrelationSifting Erdos3CorrelationMoments
  Erdos3PopularAlmostPeriods Erdos3BohrTranslation Erdos3BohrLocalAverages
  Erdos3LocalThreeAPMoment Erdos3FiniteBohr Erdos3CrootSisaskL2
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

/-- A large value of the sum forces simultaneous lower bounds under pointwise upper bounds. -/
lemma exists_two_large {I : Type*} [Fintype I] [Nonempty I]
    (f g : I → ℝ) {a b U V : ℝ}
    (hfmean : a ≤ 𝔼 i : I, f i) (hgmean : b ≤ 𝔼 i : I, g i)
    (hf : ∀ i, f i ≤ U) (hg : ∀ i, g i ≤ V) :
    ∃ i, a+b-V ≤ f i ∧ a+b-U ≤ g i := by
  obtain ⟨i,_,hi⟩ := exists_max_image (univ : Finset I) (fun i ↦ f i+g i) univ_nonempty
  have hmax : (𝔼 j : I, (f j+g j)) ≤ f i+g i := expect_le univ_nonempty hi
  rw [expect_add_distrib] at hmax
  exact ⟨i, by linarith [hg i], by linarith [hf i]⟩

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma mean_diffSmooth_exchange (B C : Finset G) (f : G → ℝ) :
    (𝔼 b : B, diffSmooth C f b) =
      𝔼 c : C, 𝔼 d : C, smooth B f ((d : G)-(c : G)) := by
  unfold diffSmooth smooth
  rw [expect_comm]
  apply expect_congr rfl
  intro c _
  rw [expect_comm]
  apply expect_congr rfl
  intro d _
  apply expect_congr rfl
  intro b _
  congr 1
  abel

/-- A symmetric average preserves the mean on a stable Bohr set if all its shifts
are within the stability window. -/
theorem mean_bohr_diffSmooth_close (D : Finset (AddChar G ℂ)) {r h δ M : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (C : Finset G) (hC : C.Nonempty)
    (hsub : ∀ c ∈ C, ∀ d ∈ C, d-c ∈ bohr D h)
    (f : G → ℝ) (hf : ∀ x, |f x| ≤ M) :
    |(𝔼 b : bohr D r, diffSmooth C f b)-(𝔼 b : bohr D r, f b)| ≤ δ*M := by
  letI : Nonempty C := hC.to_subtype
  rw [mean_diffSmooth_exchange]
  have hz : (𝔼 b : bohr D r, f b) = smooth (bohr D r) f 0 := by
    simp only [smooth, zero_add]
  rw [hz]
  have hp (c d : C) :
      |smooth (bohr D r) f ((d : G)-(c : G))-smooth (bohr D r) f 0| ≤ δ*M := by
    simpa only [zero_add] using
      smooth_bohr_translation_le D hr hh hδ hM hgrowth f hf
        (hsub c c.property d d.property) 0
  apply abs_le.mpr
  constructor
  · have hl : smooth (bohr D r) f 0-δ*M ≤
        𝔼 c : C, 𝔼 d : C, smooth (bohr D r) f ((d : G)-(c : G)) := by
      apply le_expect univ_nonempty
      intro c _
      apply le_expect univ_nonempty
      intro d _
      linarith [(abs_le.mp (hp c d)).1]
    linarith
  · have hu : (𝔼 c : C, 𝔼 d : C, smooth (bohr D r) f ((d : G)-(c : G))) ≤
        smooth (bohr D r) f 0+δ*M := by
      apply expect_le univ_nonempty
      intro c _
      apply expect_le univ_nonempty
      intro d _
      linarith [(abs_le.mp (hp c d)).2]
    linarith

/-- Under two no-increment bounds there is a common center retaining both averages. -/
theorem exists_simultaneous_averages (D : Finset (AddChar G ℂ)) {r h δ ε : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A W C : Finset G) (hW : W.Nonempty) (hC : C.Nonempty)
    (hWsub : W ⊆ bohr D h)
    (hCsub : ∀ c ∈ C, ∀ d ∈ C, d-c ∈ bohr D h)
    (hWupper : ∀ x ∈ bohr D r,
      smooth W (indicator A) x ≤ (1+ε)*relativeDensity A (bohr D r))
    (hCupper : ∀ x ∈ bohr D r,
      diffSmooth C (indicator A) x ≤ (1+ε)*relativeDensity A (bohr D r)) :
    ∃ x ∈ bohr D r,
      (1-ε)*relativeDensity A (bohr D r)-2*δ ≤ smooth W (indicator A) x ∧
      (1-ε)*relativeDensity A (bohr D r)-2*δ ≤ diffSmooth C (indicator A) x := by
  have hB : (bohr D r).Nonempty := ⟨0,bohr_zero D hr⟩
  letI : Nonempty (bohr D r) := hB.to_subtype
  have hWmean := mean_bohr_smooth_close D hr hh hδ (by norm_num : (0 : ℝ) ≤ 1)
    hgrowth W hW hWsub (indicator A) (indicator_abs_le_one A)
  have hCmean := mean_bohr_diffSmooth_close D hr hh hδ (by norm_num : (0 : ℝ) ≤ 1)
    hgrowth C hC hCsub (indicator A) (indicator_abs_le_one A)
  rw [mean_indicator_eq_relativeDensity, mul_one] at hWmean hCmean
  obtain ⟨x,hx,hx'⟩ := exists_two_large
    (fun x : bohr D r ↦ smooth W (indicator A) x)
    (fun x : bohr D r ↦ diffSmooth C (indicator A) x)
    (a := relativeDensity A (bohr D r)-δ) (b := relativeDensity A (bohr D r)-δ)
    (by linarith [(abs_le.mp hWmean).1]) (by linarith [(abs_le.mp hCmean).1])
    (fun x ↦ hWupper x x.property) (fun x ↦ hCupper x x.property)
  refine ⟨x,x.property,?_,?_⟩ <;> nlinarith

/-- Translated-window formulation, including the doubled-center weight identity. -/
theorem exists_simultaneous_windows (h2 : Function.Bijective (fun x : G ↦ x+x))
    (D : Finset (AddChar G ℂ)) {r h δ ε : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A W U C : Finset G) (hW : W.Nonempty) (hC : C.Nonempty)
    (hUW : U ⊆ W) (hWsub : W ⊆ bohr D h)
    (hCsub : ∀ c ∈ C, ∀ d ∈ C, d-c ∈ U)
    (hWupper : ∀ x ∈ bohr D r,
      smooth W (indicator A) x ≤ (1+ε)*relativeDensity A (bohr D r))
    (hCupper : ∀ x ∈ bohr D r,
      diffSmooth C (indicator A) x ≤ (1+ε)*relativeDensity A (bohr D r)) :
    ∃ x ∈ bohr D r,
      window A U x ⊆ window A W x ∧
      (1-ε)*relativeDensity A (bohr D r)-2*δ ≤ relativeDensity (window A W x) W ∧
      (1-ε)*relativeDensity A (bohr D r)-2*δ ≤
        doubledMass (window A U x) (corr (normalized (C.image (doublingEquiv G h2)))) := by
  obtain ⟨x,hx,hW',hC'⟩ := exists_simultaneous_averages D hr hh hδ hgrowth A W C hW hC
    hWsub (fun c hc d hd ↦ hWsub (hUW (hCsub c hc d hd))) hWupper hCupper
  refine ⟨x,hx,window_mono A hUW x,?_,?_⟩
  · rw [relativeDensity_window]
    exact hW'
  · rw [doubled_mass_window h2 A U C hC x hCsub]
    exact hC'

#print axioms exists_two_large
#print axioms mean_bohr_diffSmooth_close
#print axioms exists_simultaneous_windows
end Erdos3SimultaneousWindows
