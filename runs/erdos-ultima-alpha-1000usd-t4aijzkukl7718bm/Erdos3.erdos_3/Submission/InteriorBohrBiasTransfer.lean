import Submission.BiasedQuadraticBohrRefinement
import Submission.StableQuadraticDensityIncrement

/-! Bias transfer to a smaller window with an interior center. A stable
outer Bohr set loses at most twice its stability tolerance, while the
translated phase retains quadraticity on the entire boundary-buffer domain. -/
namespace Erdos3InteriorBohrBiasTransfer
open Finset Erdos3WindowBiasLocalization Erdos3StableQuadraticDensityIncrement
  Erdos3PopularAlmostPeriods Erdos3CorrelationSifting Erdos3FiniteFourier
  Erdos3FiniteBohr Erdos3BohrCovering Erdos3RelativeStableBohr Erdos3BohrTranslation
  Erdos3FixedCenterQuadraticAverage Erdos3LocalQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma excluded_center_mean (W S : Finset G) (hW : W.Nonempty) :
    density W*(𝔼 a : W, (1-indicator S a)) = density (W \ S) := by
  rw [← expect_indicator_mul W hW (fun x ↦ 1-indicator S x),← expect_indicator]
  apply expect_congr rfl
  intro a _
  by_cases hw : a ∈ W <;> by_cases hs : a ∈ S <;> simp [indicator,hw,hs]

lemma stable_interior_center_loss (D : Finset (AddChar G ℂ))
    {R : ℝ} (hR : 0 < R) {z : ℕ} (hz : 0 < z) (hst : RelativeStable D z R) :
    (𝔼 a : bohr D R, (1-indicator (bohr D (R-relativeWidth D z R)) a)) ≤ 1/(z : ℝ) := by
  have hd := density_pos (bohr D R) ⟨0,bohr_zero D hR.le⟩
  have he := excluded_center_mean (bohr D R) (bohr D (R-relativeWidth D z R)) ⟨0,bohr_zero D hR.le⟩
  have hc := stable_inner_boundary D hz hR.le hst
  have hb : density (bohr D R \ bohr D (R-relativeWidth D z R)) ≤
      1/(z : ℝ)*density (bohr D R) := by
    unfold density
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)
  rw [← he] at hb
  nlinarith

/-- The smaller averaging window T may be chosen after all geometric
parameters. The translated phase is quadratic on a fixed buffer domain. -/
theorem exists_interior_bohr_bias (D : Finset (AddChar G ℂ))
    {R : ℝ} (hR : 0 < R) {z : ℕ} (hz : 0 < z) (hst : RelativeStable D z R)
    (T : Finset G) (hT : T.Nonempty) (hTsub : T ⊆ bohr D (relativeWidth D z R))
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    {β : ℝ} (hbias : β ≤ ‖𝔼 a : bohr D R, q a‖) :
    ∃ a ∈ bohr D (R-relativeWidth D z R),
      (∀ x, ‖q (a+x)‖ = 1) ∧
      IsLocallyQuadratic (bohr D (relativeWidth D z R) : Set G) (fun x ↦ q (a+x)) ∧
      β-2/(z : ℝ) ≤ ‖𝔼 t : T, q (a+t)‖ := by
  have hw := relativeWidth_pos D hz hR
  have hwR := relativeWidth_le_quarter D hz hR.le
  have hinner : 0 ≤ R-relativeWidth D z R := by linarith
  obtain ⟨a,ha,hmean⟩ := exists_interior_biased_translate (bohr D R) T
    (bohr D (R-relativeWidth D z R)) ⟨0,bohr_zero D hR.le⟩ hT
    ⟨0,bohr_zero D hinner⟩ q (fun x ↦ (hq x).le) hbias
    (fun t ht ↦ normalized_bohr_translation_le D hR.le hw.le
      (by positivity) hst (hTsub ht))
    (stable_interior_center_loss D hR hz hst)
  refine ⟨a,ha,fun x ↦ hq _,?_,?_⟩
  · apply IsLocallyQuadratic.translate hquad a
    intro x hx
    simpa only [sub_add_cancel] using bohr_add ha hx
  · convert hmean using 1 <;> ring

#print axioms stable_interior_center_loss
#print axioms exists_interior_bohr_bias
end Erdos3InteriorBohrBiasTransfer
