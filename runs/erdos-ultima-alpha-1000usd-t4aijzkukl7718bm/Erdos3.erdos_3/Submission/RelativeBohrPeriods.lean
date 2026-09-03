import Submission.RelativeSpectrumPhase
import Submission.SpectralAlmostPeriods

/-! Relative spectral extraction of uniform almost-periods. -/
namespace Erdos3RelativeBohrPeriods
open Finset Erdos3RelativeSpectrumPhase Erdos3FiniteFourier Erdos3FiniteBohr
  Erdos3SpectralAlmostPeriods Erdos3ChangSpectrum Erdos3CorrelationSifting
  Erdos3BohrTranslation
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2500000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma shift_bound_from_walk (P : Finset G) (hP : P.Nonempty) (f : G → ℂ)
    (n : ℕ) {L η e : ℝ} (hL : (∑ χ : AddChar G ℂ, ‖hat f χ‖) ≤ L) (hη : 0 ≤ η)
    (hper : ∀ s ∈ P, ∀ t ∈ P, ∀ x, ‖f (x+s-t)-f x‖ ≤ e)
    (y : G) (hy : ∀ χ : AddChar G ℂ, 1/2 ≤ ‖meanChar P χ‖ → ‖χ y-1‖ ≤ η)
    (x : G) : ‖f (x+y)-f x‖ ≤ 2*(n : ℝ)*e+L*(η+2*(1/2 : ℝ)^(2*n)) := by
  have hs := walk_shift_bound P f n hL hη y hy x
  have h₁ := walk_close P hP f hper n (x+y)
  have h₂ := walk_close P hP f hper n x
  calc
    _ = ‖(f (x+y)-walkSmooth P n f (x+y))+
        (walkSmooth P n f (x+y)-walkSmooth P n f x)+(walkSmooth P n f x-f x)‖ := by
      congr 1
      ring
    _ ≤ (‖f (x+y)-walkSmooth P n f (x+y)‖ +
        ‖walkSmooth P n f (x+y)-walkSmooth P n f x‖)+‖walkSmooth P n f x-f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((n : ℝ)*e+L*(η+2*(1/2 : ℝ)^(2*n)))+(n : ℝ)*e :=
      add_le_add (add_le_add (by simpa only [norm_sub_rev] using h₁) hs) h₂
    _ = _ := by ring

/-- Relative Chang can be used in spectral extraction without any global density loss. -/
theorem exists_relative_almost_periods (P C : Finset G)
    (hP : P.Nonempty) (hC : C.Nonempty) (hPC : P ⊆ C)
    (f : G → ℂ) (n : ℕ) {L e ε : ℝ}
    (hL : (∑ χ : AddChar G ℂ, ‖hat f χ‖) ≤ L) (hε : 0 < ε)
    (hper : ∀ s ∈ P, ∀ t ∈ P, ∀ x, ‖f (x+s-t)-f x‖ ≤ e)
    {R : ℕ} (hR : 16*Real.log (2/((P.card : ℝ)/C.card)) < R+1)
    (herr : ε*4^(R+1) ≤ 1) :
    ∃ D : Finset (AddChar G ℂ), D ⊆ spectrum P (1/2) ∧ D.card ≤ R ∧
      ∀ {δ ρ : ℝ}, 0 ≤ δ → 0 ≤ ρ → ∀ y ∈ bohr D ρ,
        (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ δ →
        ∀ x : G, ‖f (x+y)-f x‖ ≤ 2*(n : ℝ)*e+
          L*(δ/ε+2*(D.card : ℝ)*ρ+2*(1/2 : ℝ)^(2*n)) := by
  have hR' : 4*Real.log (2/((P.card : ℝ)/C.card))/(1/2 : ℝ)^2 < R+1 := by
    convert hR using 1 <;> ring
  obtain ⟨D,hD,hcard,hphase⟩ := exists_relative_spectrum_phase P C hP hC hPC
    (η := 1/2) (by norm_num) (by norm_num) hε hR' herr
  refine ⟨D,hD,hcard,?_⟩
  intro δ ρ hδ hρ y hy hstable x
  exact shift_bound_from_walk P hP f n hL (by positivity) hper y
    (hphase hδ hρ y hy hstable) x

/-- Specialization to a stable reference Bohr set and an old-frequency window. -/
theorem exists_relative_bohr_almost_periods (P : Finset G)
    (E : Finset (AddChar G ℂ)) {r h δ : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr E (r+h)).card : ℝ) ≤ (1+δ)*((bohr E (r-h)).card : ℝ))
    (hP : P.Nonempty) (hPC : P ⊆ bohr E r)
    (f : G → ℂ) (n : ℕ) {L e ε ρ : ℝ}
    (hL : (∑ χ : AddChar G ℂ, ‖hat f χ‖) ≤ L) (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hper : ∀ s ∈ P, ∀ t ∈ P, ∀ x, ‖f (x+s-t)-f x‖ ≤ e)
    {R : ℕ} (hR : 16*Real.log (2/((P.card : ℝ)/(bohr E r).card)) < R+1)
    (herr : ε*4^(R+1) ≤ 1) :
    ∃ D : Finset (AddChar G ℂ), D ⊆ spectrum P (1/2) ∧ D.card ≤ R ∧
      ∀ y ∈ bohr (E ∪ D) (min h ρ), ∀ x : G,
        ‖f (x+y)-f x‖ ≤ 2*(n : ℝ)*e+
          L*(δ/ε+2*(D.card : ℝ)*ρ+2*(1/2 : ℝ)^(2*n)) := by
  obtain ⟨D,hD,hcard,hper'⟩ := exists_relative_almost_periods P (bohr E r) hP
    ⟨0,bohr_zero E hr⟩ hPC f n hL hε hper hR herr
  refine ⟨D,hD,hcard,?_⟩
  intro y hy x
  have hyE : y ∈ bohr E h := by
    apply mem_bohr.mpr
    intro χ hχ
    exact (mem_bohr.mp hy χ (mem_union_left _ hχ)).trans (min_le_left _ _)
  have hyD : y ∈ bohr D ρ := by
    apply mem_bohr.mpr
    intro χ hχ
    exact (mem_bohr.mp hy χ (mem_union_right _ hχ)).trans (min_le_right _ _)
  exact hper' hδ hρ y hyD (normalized_bohr_translation_le E hr hh hδ hgrowth hyE) x

#print axioms exists_relative_almost_periods
#print axioms exists_relative_bohr_almost_periods
end Erdos3RelativeBohrPeriods
