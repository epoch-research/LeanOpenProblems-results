import Submission.BiasedQuadraticTranslateFlattening

/-! A bounded-rank local flattening refinement. A biased local quadratic
phase with approximate derivative characters becomes almost invariant on a
translated inner window after adding at most 2/eta^2 Bohr frequencies. -/
namespace Erdos3BiasedQuadraticBohrRefinement
open Finset Erdos3BiasedQuadraticTranslateFlattening Erdos3BiasedPhaseSpectrum
  Erdos3LocalQuadraticPolarization Erdos3LocalQuadraticProgressions
  Erdos3LocalQuadraticInverse Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3CorrelationSifting Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3RelativeStableBohr Erdos3BohrTranslation
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def refinementError (a β ε : ℝ) (z w : ℕ) (t : ℝ) : ℝ :=
  (a+1/(z : ℝ)/ε+t+1/(w : ℝ))/(β-1/(z : ℝ))

/-- All radii and tolerances are visible. This is a flattening theorem for a
single phase, not yet a factor rank reduction or a density increment. -/
theorem exists_biased_quadratic_refinement (D : Finset (AddChar G ℂ))
    {R r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z w : ℕ} (hz : 0 < z) (hw : 0 < w)
    (hstableC : RelativeStable D z r) (hstableH : RelativeStable D w s)
    (hsr : s ≤ relativeWidth D z r)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    (F : G → AddChar G ℂ) {β a η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1) (herr : ε ≤ η^2/2)
    (hβ : 1/(z : ℝ) < β) (hbudget : η ≤ β-a-1/(z : ℝ))
    (hbias : β ≤ ‖𝔼 x : bohr D r, q x‖)
    (happrox : ∀ h ∈ bohr D s, ∀ x ∈ bohr D r,
      ‖derivative q h x-derivative q h 0*F h x‖ ≤ a) :
    ∃ E : Finset (AddChar G ℂ), (E.card : ℝ) ≤ 2/η^2 ∧
      ((D ∪ E).card : ℝ) ≤ D.card+2/η^2 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ r → t ≤ relativeWidth D z r →
        t ≤ relativeWidth D w s → r+s+t ≤ R →
        ∃ b ∈ bohr D r,
          (∀ y ∈ bohr (D ∪ E) t, ‖q (b+y)-q b‖ ≤ refinementError a β ε z w t) ∧
          ∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t,
            ‖q ((b+x)+y)-q (b+x)‖ ≤ a+1/(z : ℝ)/ε+t+refinementError a β ε z w t := by
  have hC : (bohr D r).Nonempty := ⟨0,bohr_zero D hr.le⟩
  have hst (h : G) (hh : h ∈ bohr D s) :
      (𝔼 x : G, |normalized (bohr D r) (x+h)-normalized (bohr D r) x|) ≤ 1/(z : ℝ) :=
    normalized_bohr_translation_le D hr.le (relativeWidth_pos D hz hr).le
      (by positivity) hstableC (bohr_mono D hsr hh)
  obtain ⟨E,hE,hpolar⟩ := biased_polarization_control (bohr D r) (bohr D s) hC q hq F
    hη hε hε1 herr hbudget hbias happrox hst
  refine ⟨E,hE,?_,?_⟩
  · have hc : ((D ∪ E).card : ℝ) ≤ (D.card : ℝ)+E.card := by
      exact_mod_cast card_union_le D E
    linarith
  · intro t ht htr htz htw hR
    have hleft : bohr (D ∪ E) t ⊆ bohr D t := by
      intro y hy
      exact mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hy χ (mem_union_left _ hχ))
    have hright : bohr (D ∪ E) t ⊆ bohr E t := by
      intro y hy
      exact mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hy χ (mem_union_right _ hχ))
    have hpol (x : G) (hx : x ∈ bohr D s) (y : G) (hy : y ∈ bohr (D ∪ E) t) :
        ‖localPolar q x y-1‖ ≤ a+1/(z : ℝ)/ε+t := by
      apply hpolar y (bohr_mono D htr (hleft hy)) (hright hy) _ x hx
      exact normalized_bohr_translation_le D hr.le (relativeWidth_pos D hz hr).le
        (by positivity) hstableC (bohr_mono D htz (hleft hy))
    have hsth (y : G) (hy : y ∈ bohr (D ∪ E) t) :
        (𝔼 x : G, |normalized (bohr D s) (x+y)-normalized (bohr D s) x|) ≤ 1/(w : ℝ) :=
      normalized_bohr_translation_le D hs.le (relativeWidth_pos D hw hs).le
        (by positivity) hstableH (bohr_mono D htw (hleft hy))
    exact exists_flat_bohr_translate D hr.le hs.le ht hR q hq hquad
      (bohr (D ∪ E) t) hleft hβ hbias hpol hst hsth

#print axioms exists_biased_quadratic_refinement
end Erdos3BiasedQuadraticBohrRefinement
