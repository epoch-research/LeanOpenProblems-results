import Submission.VariableRadiusQuadraticInverse
import Submission.NormalizedQuadraticDensityIncrement
import Submission.DensityPruning

/-! A quadratic phase-cell increment with a buffer at the Bohr boundary.
No buffer at phase-grid boundaries, and no progression-density transfer,
is asserted here. -/
namespace Erdos3StableQuadraticDensityIncrement
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3RelativeStableBohr
  Erdos3VariableRadiusQuadraticInverse Erdos3NormalizedQuadraticInverse
  Erdos3NormalizedQuadraticDensityIncrement Erdos3InteriorQuadraticDensityIncrement
  Erdos3NormalizedPhaseIncrement Erdos3MaskedPhaseIncrement Erdos3LocalQuadraticInverse Erdos3FiniteUniformity
  Erdos3FiniteFourier Erdos3CorrelationSifting Erdos3DensityPruning
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma stable_inner_boundary (C : Finset (AddChar G ℂ)) {z : ℕ} (hz : 0 < z)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hstable : RelativeStable C z ρ) :
    ((bohr C ρ \ bohr C (ρ-relativeWidth C z ρ)).card : ℝ) ≤
      1/(z : ℝ)*((bohr C ρ).card : ℝ) := by
  have hw : 0 ≤ relativeWidth C z ρ := by unfold relativeWidth; positivity
  have hsub : bohr C (ρ-relativeWidth C z ρ) ⊆ bohr C ρ :=
    bohr_mono C (sub_le_self _ hw)
  have hsub' : bohr C ρ ⊆ bohr C (ρ+relativeWidth C z ρ) :=
    bohr_mono C (le_add_of_nonneg_right hw)
  have hc : ((bohr C (ρ-relativeWidth C z ρ)).card : ℝ) ≤ (bohr C ρ).card := by
    exact_mod_cast card_le_card hsub
  have hc' : ((bohr C ρ).card : ℝ) ≤ (bohr C (ρ+relativeWidth C z ρ)).card := by
    exact_mod_cast card_le_card hsub'
  have he : ((bohr C ρ \ bohr C (ρ-relativeWidth C z ρ)).card : ℝ) +
      ((bohr C (ρ-relativeWidth C z ρ)).card : ℝ) = (bohr C ρ).card := by
    exact_mod_cast card_sdiff_add_card_eq_card hsub
  have hg := hc'.trans hstable
  calc
    _ ≤ 1/(z : ℝ)*((bohr C (ρ-relativeWidth C z ρ)).card : ℝ) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

lemma phase_cell_restrict {n : ℕ} {B B' S : Finset G} {q : G → ℂ}
    (hcell : IsInteriorPhaseCell n B q S) (hsub : B' ⊆ B) :
    IsInteriorPhaseCell n B' q (S ∩ B') := by
  obtain ⟨i,rfl⟩ := hcell
  refine ⟨i,?_⟩
  ext x
  simp only [mem_inter,mem_filter]
  constructor
  · rintro ⟨⟨_,hi⟩,hx⟩
    exact ⟨hx,hi⟩
  · rintro ⟨hx,hi⟩
    exact ⟨⟨hsub hx,hi⟩,hx⟩

/-- A stable radius with precision at least 65536/r^4 lets us remove the
Bohr boundary while retaining half the relative size and half the density
gain. The inner phase cell has a positive-width Bohr buffer. -/
theorem stable_inner_quadratic_density_increment
    (h2 : Function.Bijective (fun x : G ↦ x+x)) (A : Finset G)
    {δ r : ℝ} (hδ : 0 < δ)
    (hU : δ ≤ uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)))
    (hr : 0 < r) (hrcorr : r ≤ normalizedCorrelation δ)
    {z : ℕ} (hz : 0 < z) (hprecision : 65536/r^4 ≤ (z : ℝ)) :
    ∃ C : Finset (AddChar G ℂ), ∃ ρ : ℝ, ∃ q : G → ℂ, ∃ a : G, ∃ S : Finset G,
      C.card ≤ normalizedRank δ ∧ 1/64 ≤ ρ ∧ ρ ≤ 1/32 ∧
      RelativeStable C z ρ ∧ (∀ x, ‖q x‖ = 1) ∧
      IsLocallyQuadratic (bohr C (1/16) : Set G) q ∧
      IsInteriorPhaseCell (phaseResolution r) (bohr C (ρ-relativeWidth C z ρ)) q S ∧
      S.Nonempty ∧ r^3/4096*((bohr C ρ).card : ℝ) ≤ (S.card : ℝ) ∧
      density A+r/32 ≤ ((S.filter (fun x ↦ a+x ∈ A)).card : ℝ)/(S.card : ℝ) := by
  have hf (x : G) : ‖((indicator A x-density A : ℝ) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using centered_indicator_bound A x
  obtain ⟨C,ρ,q,hC,hρ,hρmax,hstable,hq,hquad,hcorr⟩ :=
    stable_radius_local_quadratic_inverse h2 _ hf hδ hU hz
  have hρ0 : 0 < ρ := by linarith
  have hQ : (bohr C ρ).Nonempty := ⟨0,bohr_zero C hρ0.le⟩
  obtain ⟨a,S,hcell,hS,hcard,hinc⟩ := normalized_phase_density_increment (bohr C ρ) hQ A q
    (fun a x ↦ (hq a x).le) hr (hrcorr.trans hcorr)
  let T := S ∩ bohr C (ρ-relativeWidth C z ρ)
  have hsub : T ⊆ S := inter_subset_left
  have hw := relativeWidth_pos C hz hρ0
  have hinner : bohr C (ρ-relativeWidth C z ρ) ⊆ bohr C ρ :=
    bohr_mono C (sub_le_self _ hw.le)
  have hprec : 1/(z : ℝ) ≤ r^4/65536 := by
    have hh := (div_le_iff₀ (pow_pos hr 4)).mp hprecision
    apply (div_le_iff₀ (show (0 : ℝ) < z by exact_mod_cast hz)).mpr
    nlinarith only [hh]
  have hloss : ((S \ T).card : ℝ) ≤ (r/16)/2*(S.card : ℝ) := by
    have hsdiff : S \ T ⊆ bohr C ρ \ bohr C (ρ-relativeWidth C z ρ) := by
      intro x hx
      obtain ⟨hx,hxt⟩ := mem_sdiff.mp hx
      refine mem_sdiff.mpr ⟨hcell.subset hx,?_⟩
      intro hxi
      exact hxt (mem_inter.mpr ⟨hx,hxi⟩)
    calc
      _ ≤ ((bohr C ρ \ bohr C (ρ-relativeWidth C z ρ)).card : ℝ) := by
        exact_mod_cast card_le_card hsdiff
      _ ≤ 1/(z : ℝ)*((bohr C ρ).card : ℝ) := stable_inner_boundary C hz hρ0.le hstable
      _ ≤ r^4/65536*((bohr C ρ).card : ℝ) :=
        mul_le_mul_of_nonneg_right hprec (Nat.cast_nonneg _)
      _ = (r/16)/2*(r^3/2048*((bohr C ρ).card : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)
  obtain ⟨hT,hTcard,hTinc⟩ := density_increment_pruning S T (fun x ↦ a+x ∈ A)
    hS hsub (density_nonneg A) (by positivity : 0 < r/16) hinc hloss
  refine ⟨C,ρ,q a,a,T,hC,hρ,hρmax,hstable,hq a,hquad a,
    phase_cell_restrict hcell hinner,hT,?_,?_⟩
  · nlinarith only [hcard,hTcard]
  · simpa only [div_div,show (16 : ℝ)*2 = 32 by norm_num] using hTinc

#print axioms stable_inner_quadratic_density_increment
end Erdos3StableQuadraticDensityIncrement
