import Submission.LocalQuadraticPolarization
import Submission.LocalCharacterEnergy

/-! A common Bohr window supporting approximate character representations of
all derivatives of any locally quadratic phase. Correlation losses are
independent of the final translation tolerance. -/
namespace Erdos3BohrDerivativeCharacters
open Finset Erdos3LocalQuadraticPolarization Erdos3LocalCharacterEnergy
  Erdos3LocalQuadraticProgressions Erdos3LocalQuadraticInverse
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3CorrelationSifting
  Erdos3FiniteBohr Erdos3BohrCovering Erdos3FourierSmoothing
  Erdos3RelativeStableBohr Erdos3BohrTranslation
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000
set_option linter.style.existsImplication false

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- All overlap translations are covered: they are differences of two
points of the inner Bohr set and therefore lie in the larger domain. -/
lemma polar_overlap (D : Finset (AddChar G ℂ)) {R r : ℝ}
    (hr : 0 < r) (hrr : r ≤ R/4) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    {h : G} (hh : h ∈ bohr D (R/4)) (y x : G)
    (hx : x ∈ bohr D r) (hxy : x+y ∈ bohr D r) :
    localPolar q h (x+y) = localPolar q h y*localPolar q h x := by
  have hR : 0 < R := by linarith
  have hy : y ∈ bohr D (2*r) := by
    simpa only [show (x+y)+ -x = y by abel,show r+r = 2*r by ring] using
      bohr_add hxy (bohr_neg hx)
  rw [localPolar_add hq hquad h x y
    (bohr_zero D hR.le)
    (bohr_mono D (by linarith : R/4 ≤ R) hh)
    (bohr_mono D (by linarith : r ≤ R) hx)
    (bohr_mono D (by linarith : r+R/4 ≤ R) (bohr_add hx hh))
    (bohr_mono D (by linarith : 2*r ≤ R) hy)
    (bohr_mono D (by linarith : 2*r+R/4 ≤ R) (bohr_add hy hh))
    (bohr_mono D (by linarith : r ≤ R) hxy)
    (bohr_mono D (by linarith : r+R/4 ≤ R) (bohr_add hxy hh)),mul_comm]

/-- Character approximation on a fixed inner Bohr set. -/
theorem exists_bohr_polar_character (D : Finset (AddChar G ℂ)) {R r : ℝ}
    (hr : 0 < r) (hrr : r ≤ R/4) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    {h : G} (hh : h ∈ bohr D (R/4))
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : ρ^2 ≤ density (bohr D r)) :
    ∃ ψ : AddChar G ℂ,
      ∀ y : G, ∀ δ : ℝ,
        (𝔼 x : G, |normalized (bohr D r) (x+y)-normalized (bohr D r) x|) ≤ δ →
          ‖localPolar q h y-ψ y‖ ≤ δ/ρ := by
  obtain ⟨ψ,_,hψ⟩ := exists_energy_local_character (bohr D r) ⟨0,bohr_zero D hr.le⟩
    (localPolar q h) (localPolar q h) (localPolar_norm q hq h)
    (localPolar_norm q hq h) (polar_overlap D hr hrr q hq hquad hh) hρ hsize
  refine ⟨ψ,?_⟩
  intro y δ hδ
  rw [norm_sub_rev]
  exact hψ y (localPolar q h y) (localPolar_norm q hq h y)
    (polar_overlap D hr hrr q hq hquad hh y) δ hδ

/-- The stable radius is chosen before the phase, and the lower bound on rho
uses only the fixed radius R/8. No circular dependence on z occurs. -/
theorem exists_stable_derivative_characters (D : Finset (AddChar G ℂ))
    {R : ℝ} (hR : 0 < R) {z : ℕ} (hz : 0 < z)
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : ρ^2 ≤ density (bohr D (R/8))) :
    ∃ r : ℝ, R/8 ≤ r ∧ r ≤ R/4 ∧ RelativeStable D z r ∧
      ∀ q : G → ℂ, (∀ x, ‖q x‖ = 1) →
        IsLocallyQuadratic (bohr D R : Set G) q →
        ∃ F : G → AddChar G ℂ,
          ∀ h ∈ bohr D (R/4), ∀ y ∈ bohr D (relativeWidth D z r),
            ‖derivative q h y-derivative q h 0*F h y‖ ≤ 1/((z : ℝ)*ρ) := by
  obtain ⟨r,hr₁,hr₂,hs⟩ := exists_relative_stable D (show 0 < R/8 by positivity) hz
  have hr : 0 < r := (show 0 < R/8 by positivity).trans_le hr₁
  have hrr : r ≤ R/4 := by linarith
  have hsize' : ρ^2 ≤ density (bohr D r) := by
    apply hsize.trans
    unfold density
    gcongr
    exact bohr_mono D hr₁
  refine ⟨r,hr₁,hrr,hs,?_⟩
  intro q hq hquad
  have hex (h : G) : ∃ ψ : AddChar G ℂ, h ∈ bohr D (R/4) →
      ∀ y ∈ bohr D (relativeWidth D z r),
        ‖localPolar q h y-ψ y‖ ≤ 1/((z : ℝ)*ρ) := by
    by_cases hh : h ∈ bohr D (R/4)
    · obtain ⟨ψ,hψ⟩ := exists_bohr_polar_character D hr hrr q hq hquad hh hρ hsize'
      refine ⟨ψ,fun _ y hy ↦ ?_⟩
      have ht := normalized_bohr_translation_le D hr.le
        (relativeWidth_pos D hz hr).le (by positivity : (0 : ℝ) ≤ 1/(z : ℝ)) hs hy
      simpa only [div_div] using hψ y (1/(z : ℝ)) ht
    · exact ⟨1,fun h ↦ (hh h).elim⟩
  choose F hF using hex
  refine ⟨F,?_⟩
  intro h hh y hy
  have he : derivative q h y-derivative q h 0*F h y =
      derivative q h 0*(localPolar q h y-F h y) := by
    rw [derivative_eq_localPolar q hq h y]
    ring
  rw [he,norm_mul,derivative_norm_one q hq,one_mul]
  exact hF h hh y hy

#print axioms exists_bohr_polar_character
#print axioms exists_stable_derivative_characters
end Erdos3BohrDerivativeCharacters
