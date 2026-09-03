import Submission.JointGraphAlmostPeriods
import Submission.RelativeBohrPeriods

/-! One Chang spectrum simultaneously controls all phase-cubic functions
sharing the graph sample set. Its rank is logarithmic in that set's density. -/
namespace Erdos3CommonCubicBohrPeriods
open Finset Erdos3FiniteFourier Erdos3FiniteBohr Erdos3ChangSpectrum
  Erdos3RelativeBohrPeriods Erdos3SpectralAlmostPeriods Erdos3CorrelationSifting
  Erdos3PhaseCubicSmoothing Erdos3GraphTripleProjection Erdos3JointGraphAlmostPeriods
  Erdos3UnlocalizedBilinearExtraction Erdos3LocalQuadraticIntegration Erdos3BiasedSkewDifferences
  Erdos3AntidiagonalTwistedEnergy Erdos3PopularAlmostPeriods Erdos3SpectralGraphEnergy
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The generating spectrum depends only on the common almost-period set X,
not on the individual function, its error, or the walk length. -/
theorem exists_common_bohr_generators (X : Finset G) (hX : X.Nonempty) :
    ∃ E : Finset (AddChar G ℂ), E.card ≤ ⌊16*Real.log (1/density X)⌋₊ ∧
      ∀ (f : G → ℂ) (ℓ : ℕ) (L e τ : ℝ), 0 ≤ τ →
        (∑ χ : AddChar G ℂ, ‖hat f χ‖) ≤ L →
        (∀ s ∈ X, ∀ t ∈ X, ∀ x, ‖f (x+s)-f (x+t)‖ ≤ e) →
        ∀ y ∈ bohr E (τ/((E.card : ℝ)+1)), ∀ x,
          ‖f (x+y)-f x‖ ≤ 2*(ℓ : ℝ)*e+L*(τ+2*(1/2 : ℝ)^(2*ℓ)) := by
  obtain ⟨E,_,hcard,hspan⟩ := exists_spectrum_generators X hX (η := 1/2) (by norm_num) (by norm_num)
  have he : 4*Real.log (1/density X)/(1/2 : ℝ)^2 = 16*Real.log (1/density X) := by ring
  rw [he] at hcard
  refine ⟨E,hcard,?_⟩
  intro f ℓ L e τ hτ hL hper y hy x
  apply shift_bound_from_walk X hX f ℓ hL hτ
    (fun s hs t ht z ↦ by simpa only [sub_add_cancel,show z-t+s = z+s-t by abel] using hper s hs t ht (z-t)) y _ x
  intro χ hχ
  have hχ' : χ ∈ spectrum X (1/2) := by
    simpa only [Erdos3ChangSpectrum.spectrum,meanChar,mem_filter,mem_univ,true_and] using hχ
  have hh := span_control E (hspan hχ') (show 0 ≤ τ/((E.card : ℝ)+1) by positivity) hy
  apply hh.trans
  rw [← mul_div_assoc,div_le_iff₀ (by positivity : (0 : ℝ) < E.card+1)]
  nlinarith

lemma cubicSmooth_one (T : Finset G) (hT : T.Nonempty) (x : G) :
    cubicSmooth T (fun _ ↦ 1) x = (triple T x : ℂ) := by
  rw [cubicSmooth_eq T hT]
  simp only [triple,diffSmooth,ofReal_expect]
  apply expect_congr rfl
  intro b _
  apply expect_congr rfl
  intro a _
  simp only [phaseMask,indicator,map_one,mul_one,sub_add_eq_add_sub]
  split_ifs <;> simp

lemma triple_hat_l1_le_one (T : Finset G) (hT : T.Nonempty) :
    (∑ χ : AddChar G ℂ, ‖hat (fun x ↦ (triple T x : ℂ)) χ‖) ≤ 1 := by
  have he : (fun x ↦ (triple T x : ℂ)) = cubicSmooth T (fun _ ↦ 1) := by
    funext x
    exact (cubicSmooth_one T hT x).symm
  rw [he]
  exact cubicSmooth_hat_l1_le_one T hT _ (fun _ ↦ by simp)

/-- The same Bohr set controls the scalar triple convolution and every biased
skew-phase cubic convolution. Its rank does not include the number of phases. -/
theorem exists_common_cubic_bohr_periods (T : Finset G) (h0 : (0 : G) ∈ T)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {n : ℕ} (hn : 0 < n) {η ε τ : ℝ} (hη : 0 < η) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hL2 : 8 ≤ (n : ℝ)*ε^2)
    (hspec : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*η^4*ε^2) (ℓ : ℕ) :
    ∃ X : Finset G, ∃ E : Finset (AddChar G ℂ), X.Nonempty ∧ X ⊆ T ∧
      T.card^n*T.card ≤ 2*(Fintype.card G)^n*X.card ∧
      E.card ≤ ⌊16*Real.log (1/density X)⌋₊ ∧
      (∀ y ∈ bohr E (τ/((E.card : ℝ)+1)), ∀ x,
        |triple T (x+y)-triple T x| ≤ 4*(ℓ : ℝ)*ε+τ+2*(1/2 : ℝ)^(2*ℓ)) ∧
      ∀ d : G, η ≤ normalizedSkewBias T F d →
        ∀ y ∈ bohr E (τ/((E.card : ℝ)+1)), ∀ x,
          ‖cubicSmooth T (fun z ↦ skewPhase F z d) (x+y)-
            cubicSmooth T (fun z ↦ skewPhase F z d) x‖ ≤ 4*(ℓ : ℝ)*ε+τ+2*(1/2 : ℝ)^(2*ℓ) := by
  obtain ⟨X,hX,hXT,hsize,hscalar,hphase⟩ := exists_skew_cubic_almost_periods T h0 F hF hdiff hn hη hε hL2 hspec
  obtain ⟨E,hE,hcommon⟩ := exists_common_bohr_generators X hX
  refine ⟨X,E,hX,hXT,hsize,hE,?_,?_⟩
  · intro y hy x
    have hp := hcommon (fun x ↦ (triple T x : ℂ)) ℓ 1 ε τ hτ (triple_hat_l1_le_one T ⟨0,h0⟩)
      (fun s hs t ht x ↦ by simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hscalar s hs t ht x) y hy x
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,one_mul] at hp
    have hnR : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    nlinarith
  · intro d hd y hy x
    have hp := hcommon (cubicSmooth T (fun z ↦ skewPhase F z d)) ℓ 1 (2*ε) τ hτ
      (cubicSmooth_hat_l1_le_one T ⟨0,h0⟩ _ (fun z ↦ (skewPhase_norm F z d).le))
      (fun s hs t ht x ↦ hphase s hs t ht d hd x) y hy x
    convert hp using 1 <;> ring

#print axioms exists_common_cubic_bohr_periods
end Erdos3CommonCubicBohrPeriods
