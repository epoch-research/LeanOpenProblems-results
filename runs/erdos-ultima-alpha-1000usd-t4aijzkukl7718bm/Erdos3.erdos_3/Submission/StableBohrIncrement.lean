import Submission.CorrelationIncrement
import Submission.BohrLocalAverages

/-! The global correlation criterion can output a fixed-tolerance stable Bohr set.
This does not yet supply an iteratable localized density-increment theorem. -/
namespace Erdos3StableBohrIncrement
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrStableScale Erdos3BohrTranslation
  Erdos3CorrelationIncrement Erdos3CorrelationMoments Erdos3PopularAlmostPeriods Erdos3CrootSisaskL2
open scoped BigOperators Classical
set_option maxHeartbeats 1500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Any correlation gain throughout a Bohr set can be realized on a smaller stable Bohr set,
without losing the gain factor. -/
theorem exists_stable_bohr_increment (B : Finset G) (hB : B.Nonempty)
    (D : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 0 < ρ) {q : ℕ} (hq : 0 < q)
    (g f : G → ℝ) (hg : ∀ x, 0 ≤ g x) (hmean : (𝔼 x : G, g x) = 1)
    {H c : ℝ} (hH : 0 ≤ H) (hfc : ∀ x, H*f x ≤ corr g x)
    (hpop : ∀ t ∈ bohr D ρ, c ≤ diffSmooth B f t) :
    ∃ r : ℝ,
      ρ/4 ≤ r-stabilityWidth D q (ρ/4) ∧
      r+stabilityWidth D q (ρ/4) ≤ ρ/2 ∧
      ((bohr D (r+stabilityWidth D q (ρ/4))).card : ℝ) ≤
        (1+1/(q : ℝ))*((bohr D (r-stabilityWidth D q (ρ/4))).card : ℝ) ∧
      ∃ x : G, H*c ≤ smooth (bohr D r) g x := by
  obtain ⟨r,hrlo,hrhi,hgrowth⟩ := exists_stable_radius D (by positivity : 0 < ρ/4) hq
  have hwidth := stabilityWidth_pos D hq (by positivity : 0 < ρ/4)
  have hr : 0 < r := by linarith
  have hr2 : 2*r ≤ ρ := by linarith
  refine ⟨r,hrlo,by linarith,hgrowth,?_⟩
  apply exists_translate_increment B (bohr D r) hB ⟨0,bohr_zero D hr.le⟩ g hg hmean
  intro s hs t ht
  have hst : s-t ∈ bohr D ρ := by
    have h := bohr_add hs (bohr_neg ht)
    apply bohr_mono D (by linarith) (show s-t ∈ bohr D (r+r) by simpa [sub_eq_add_neg] using h)
  calc
    H*c ≤ H*diffSmooth B f (s-t) := mul_le_mul_of_nonneg_left (hpop _ hst) hH
    _ = diffSmooth B (fun y ↦ H*f y) (s-t) := (diffSmooth_const_mul ..).symm
    _ ≤ _ := diffSmooth_mono B _ _ hfc _

#print axioms exists_stable_bohr_increment
end Erdos3StableBohrIncrement
