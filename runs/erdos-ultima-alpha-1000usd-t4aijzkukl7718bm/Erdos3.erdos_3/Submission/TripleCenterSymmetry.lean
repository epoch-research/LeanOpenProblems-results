import Submission.CommonCubicBohrPeriods

/-! A dense-set triple convolution has a large center. Simultaneous scalar
and phase-cubic periods at this center force approximate skew annihilation. -/
namespace Erdos3TripleCenterSymmetry
open Finset Erdos3CrootSisaskL2 Erdos3FiniteSamplingMoments Erdos3CorrelationSifting
  Erdos3PopularAlmostPeriods Erdos3SpectralGraphEnergy Erdos3GraphTripleProjection
  Erdos3PhaseCubicSmoothing Erdos3UnlocalizedBilinearExtraction Erdos3LocalQuadraticIntegration
  Erdos3LocalSkewSymmetry Erdos3AntidiagonalTwistedEnergy Erdos3BiasedSkewDifferences
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma smooth_indicator_mean (T : Finset G) (hT : T.Nonempty) :
    (𝔼 x : G, smooth T (indicator T) x) = density T := by
  letI : Nonempty T := hT.to_subtype
  unfold smooth
  rw [expect_comm]
  have he (a : T) : (𝔼 x, indicator T (x+(a : G))) = density T := by
    calc
      _ = 𝔼 x, indicator T x := Fintype.expect_equiv (Equiv.addRight (a : G)) _ _ (fun _ ↦ rfl)
      _ = _ := expect_indicator T
  simp only [he,Fintype.expect_const]

lemma smooth_square_triple (T : Finset G) (hT : T.Nonempty) :
    (𝔼 x : G, (smooth T (indicator T) x)^2) = density T*(𝔼 y : T, triple T y) := by
  have he (a b : T) : (𝔼 x, indicator T (x+(a : G))*indicator T (x+b)) =
      density T*(𝔼 y : T, indicator T ((y : G)+b-a)) := by
    calc
      _ = 𝔼 y, indicator T y*indicator T (y+(b : G)-a) :=
        Fintype.expect_equiv (Equiv.addRight (a : G)) _ _ (fun x ↦ by
          simp only [Equiv.coe_addRight,show x+(a : G)+b-a = x+b by abel])
      _ = _ := expect_indicator_mul T hT _
  calc
    _ = 𝔼 x : G, 𝔼 a : T, 𝔼 b : T, indicator T (x+(a : G))*indicator T (x+b) := by
      simp only [smooth,sq,Fintype.expect_mul_expect]
    _ = 𝔼 a : T, 𝔼 b : T, 𝔼 x : G, indicator T (x+(a : G))*indicator T (x+b) := (expect_rotate_three _).symm
    _ = density T*(𝔼 a : T, 𝔼 b : T, 𝔼 y : T, indicator T ((y : G)+b-a)) := by
      simp only [he,← mul_expect]
    _ = _ := by rw [expect_rotate_three]; rfl

/-- The average triple convolution on T is at least density(T). -/
lemma triple_mean_lower (T : Finset G) (hT : T.Nonempty) :
    density T ≤ 𝔼 y : T, triple T y := by
  have hσ := density_pos T hT
  have hh := expect_even_pow_le (by decide : Even 2) (smooth T (indicator T))
  rw [smooth_indicator_mean T hT,smooth_square_triple T hT] at hh
  exact (mul_le_mul_iff_right₀ hσ).mp (by simpa only [sq] using hh)

theorem exists_large_triple_center (T : Finset G) (hT : T.Nonempty) :
    ∃ a ∈ T, density T ≤ triple T a := by
  letI : Nonempty T := hT.to_subtype
  obtain ⟨a,_,ha⟩ := exists_max_image univ (fun a : T ↦ triple T a) univ_nonempty
  exact ⟨a,a.property,(triple_mean_lower T hT).trans (expect_le univ_nonempty ha)⟩

lemma scalar_comparison_phase_bound (z : ℂ) (hz : ‖z‖ = 1) {r s σ ρ : ℝ}
    (hs : σ ≤ s) (hσ : 0 ≤ σ) (hscalar : |r-s| ≤ ρ) (hphase : ‖z*(r : ℂ)-(s : ℂ)‖ ≤ ρ) :
    σ*‖z-1‖ ≤ 2*ρ := by
  have hs0 : 0 ≤ s := hσ.trans hs
  have he : (z-1)*(s : ℂ) = z*((s-r : ℝ) : ℂ)+(z*(r : ℂ)-(s : ℂ)) := by push_cast; ring
  have hh : ‖(z-1)*(s : ℂ)‖ ≤ 2*ρ := by
    rw [he]
    calc
      _ ≤ ‖z*((s-r : ℝ) : ℂ)‖+‖z*(r : ℂ)-(s : ℂ)‖ := norm_add_le _ _
      _ ≤ ρ+ρ := by
        apply add_le_add _ hphase
        simpa only [norm_mul,hz,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] using hscalar
      _ = _ := by ring
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs0] at hh
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans (by nlinarith only [hh])

/-- Positivity at one large center makes every common scalar period lie in the
local additivity domain. The phase periods then approximately annihilate all
biased skew phases, with no loss depending on the sample-set density. -/
theorem common_periods_force_skew (T : Finset G) (h0 : (0 : G) ∈ T)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (P : Finset G) {η ρ : ℝ} (hρ : ρ < density T)
    (hscalar : ∀ t ∈ P, ∀ x, |triple T (x+t)-triple T x| ≤ ρ)
    (hphase : ∀ d : G, η ≤ normalizedSkewBias T F d → ∀ t ∈ P, ∀ x,
      ‖cubicSmooth T (fun y ↦ skewPhase F y d) (x+t)-cubicSmooth T (fun y ↦ skewPhase F y d) x‖ ≤ ρ) :
    P ⊆ diffBall T 4 ∧ ∀ d : G, η ≤ normalizedSkewBias T F d → ∀ t ∈ P,
      density T*‖skewPhase F t d-1‖ ≤ 2*ρ := by
  have hT : T.Nonempty := ⟨0,h0⟩
  have hσ := density_pos T hT
  obtain ⟨a,ha,hcenter⟩ := exists_large_triple_center T hT
  have hpositive (t : G) (ht : t ∈ P) : 0 < triple T (a+t) := by
    have hh := hscalar t ht a
    linarith [(abs_le.mp hh).1]
  have hP : P ⊆ diffBall T 4 := by
    intro t ht
    have h3 := triple_mem_diffBall h0 (hpositive t ht).ne'
    have h1 := subset_diffBall_one T h0 ha
    simpa only [show a+t-a = t by abel] using diffBall_sub h3 h1
  refine ⟨hP,?_⟩
  intro d hd t ht
  have hsum : a+t ∈ diffBall T 4 := diffBall_mono T hT (by decide)
    (triple_mem_diffBall h0 (hpositive t ht).ne')
  have hsa := diffBall_mono T hT (by decide : 1 ≤ 4) (subset_diffBall_one T h0 ha)
  have hadd := skewPhase_add_left hF hsa (hP ht) hsum d
  have hp := hphase d hd t ht a
  rw [cubicSmooth_skew_factor T h0 F hF,cubicSmooth_skew_factor T h0 F hF,hadd] at hp
  have he : skewPhase F a d*skewPhase F t d*(triple T (a+t) : ℂ)-
      skewPhase F a d*(triple T a : ℂ) =
      skewPhase F a d*(skewPhase F t d*(triple T (a+t) : ℂ)-(triple T a : ℂ)) := by ring
  rw [he,norm_mul,skewPhase_norm,one_mul] at hp
  exact scalar_comparison_phase_bound _ (skewPhase_norm F t d) hcenter hσ.le (hscalar t ht a) hp

#print axioms exists_large_triple_center
#print axioms common_periods_force_skew
end Erdos3TripleCenterSymmetry
