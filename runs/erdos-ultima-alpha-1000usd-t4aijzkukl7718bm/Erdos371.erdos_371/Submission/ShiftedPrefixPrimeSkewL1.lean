import Submission.ShiftedPrefixOddEnergy
import Submission.HarmonicPrefixPrimeSkewL1

/-! Prime-gap skew cancellation in the absolute mixture of ordinary
prefixes over a moving harmonic window. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory DilationSpectrum AbelPrimes
open scoped Topology
set_option autoImplicit false

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def shiftedPrefixPrimeSkewL1 (A N : ℕ) (L : ℕ → X)
    (P : Finset ℕ) (C : Fin (N+1) → X → X → ℝ) : ℝ :=
  mean (shiftedEndpointLaw A N) (fun i => |naturalPrimeSkewAverage (shiftedEndpoint A N i) L P (C i)|)

lemma shiftedPrefixPrimeSkewL1_energy_bound (A N R : ℕ) (L : ℕ → X)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (C : Fin (N+1) → X → X → ℝ)
    (hC : ∀ i a b, C i b a = -C i a b) (hCb : ∀ i a b, |C i a b| ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    2*shiftedPrefixPrimeSkewL1 A N L P C ≤ Fintype.card X*η+
      (∑ b, shiftedPrefixOddEnergy A N L P b)/η+8*R/shiftedHarmonicMass A N := by
  have hcyc := componentwise_cyclicPrimeSkewAverage_energy_bound (shiftedEndpoint A N)
    (shiftedEndpointLaw A N) (fun _ x => L x.val) P C hC hCb η hη
  rw [mean_finset_sum] at hcyc
  change 2*mean (shiftedEndpointLaw A N) (fun i =>
    |cyclicPrimeSkewAverage (shiftedEndpoint A N i) (fun x => L x.val) P (C i)|) ≤
      Fintype.card X*η+(∑ b, shiftedPrefixOddEnergy A N L P b)/η at hcyc
  have hcomp (i : Fin (N+1)) : |naturalPrimeSkewAverage (shiftedEndpoint A N i) L P (C i)| ≤
      |cyclicPrimeSkewAverage (shiftedEndpoint A N i) (fun x => L x.val) P (C i)|+
        2*R/(shiftedEndpoint A N i : ℝ) := by
    have he := naturalPrimeSkewAverage_cyclic_error (shiftedEndpoint A N i) R L P hP (C i) (hCb i)
    have ht := abs_sub_le (naturalPrimeSkewAverage (shiftedEndpoint A N i) L P (C i))
      (cyclicPrimeSkewAverage (shiftedEndpoint A N i) (fun x => L x.val) P (C i)) 0
    simp only [sub_zero] at ht
    linarith
  have hm := mean_mono (shiftedEndpointLaw A N) _ _ hcomp
  rw [mean_add] at hm
  have he : (fun i : Fin (N+1) => 2*(R : ℝ)/(shiftedEndpoint A N i : ℝ)) =
      (fun i => (2*(R : ℝ))*((1 : ℝ)/shiftedEndpoint A N i)) := by funext i; ring
  rw [he,mean_const_mul] at hm
  have hr := mul_le_mul_of_nonneg_left (shiftedEndpointLaw_reciprocal_bound A N)
    (show 0 ≤ 2*(R : ℝ) by positivity)
  have heq : (2*(R : ℝ))*(2/shiftedHarmonicMass A N) = 4*R/shiftedHarmonicMass A N := by ring
  rw [heq] at hr
  change shiftedPrefixPrimeSkewL1 A N L P C ≤ _ at hm
  rw [show 8*(R : ℝ)/shiftedHarmonicMass A N = 2*(4*(R : ℝ)/shiftedHarmonicMass A N) by ring]
  linarith

variable [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Choose the large prime-band starting scale using the common word law.
For each subsequent FIXED band scale, the entire L1 mixture is eventually
small, uniformly over all bounded skew component observables. -/
theorem shiftedPrefixPrimeSkewL1_narrow_eventually
    (L : ℕ → X) (A M : ℕ → ℕ)
    (hmass : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (μ : ProbabilityMeasure (ℕ → X))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ))
    (hμ : MeasurePreserving wordShift (μ : Measure (ℕ → X)) (μ : Measure (ℕ → X)))
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → X) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂(μ : Measure (ℕ → X))) ≤
        p*∫ x, F (fun k => x (p*k)) ∂(μ : Measure (ℕ → X)))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ᶠ j : ℕ in atTop,
      ∀ C : Fin (M j+1) → X → X → ℝ,
        (∀ i x y, C i y x = -C i x y) → (∀ i x y, |C i x y| ≤ 1) →
          shiftedPrefixPrimeSkewL1 (A j) (M j) L (narrowPrimeBand a b H) C < ε := by
  let η : ℝ := ε/(4*(Fintype.card X+1 : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hcoef : (Fintype.card X : ℝ)*η < ε/4 := by
    have he : η*(4*(Fintype.card X+1 : ℝ))=ε := by dsimp [η]; field_simp
    nlinarith
  let E (H : ℕ) : ℝ := ∑ z : X, ∫ x, (wordOddAverage (linearPrimeEndpoint b H)
    (narrowPrimeBand a b H) (labelIndicator z) x)^2 ∂(μ : Measure (ℕ → X))
  have hE : Tendsto E atTop (𝓝 0) := by
    have ht := tendsto_finset_sum (univ : Finset X) (fun z _ =>
      stationary_wordOddAverage_narrow_prime_energy_zero (μ : Measure (ℕ → X)) hμ hdom
        (labelIndicator z) a b ha hab)
    simpa only [sum_const_zero] using ht
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp
    (hE.eventually_lt_const (by positivity : (0 : ℝ)<η*ε/4))
  refine ⟨H₀,?_⟩
  intro H hH
  have hlimE : Tendsto (fun j => ∑ z, shiftedPrefixOddEnergy (A j) (M j) L (narrowPrimeBand a b H) z)
      atTop (𝓝 (E H)) := by
    exact tendsto_finset_sum (univ : Finset X) (fun z _ => shiftedPrefixOddEnergy_limit L A M hmass μ hlim
      (linearPrimeEndpoint b H) (narrowPrimeBand a b H)
      (fun p hp => (narrowPrimeBand_member_bounds a b H p hp).2) z)
  have hsmallE := hlimE.eventually_lt_const
    (show E H < η*ε/2 by have hh := hH₀ H hH; nlinarith)
  have ht : Tendsto (fun j => 8*(linearPrimeEndpoint b H : ℝ)/shiftedHarmonicMass (A j) (M j))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hmass
  filter_upwards [hsmallE,ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with j hj htail
  intro C hC hCb
  have hb := shiftedPrefixPrimeSkewL1_energy_bound (A j) (M j) (linearPrimeEndpoint b H) L
    (narrowPrimeBand a b H) (fun p hp => (narrowPrimeBand_member_bounds a b H p hp).2) C hC hCb η hη
  have hdiv : (∑ z, shiftedPrefixOddEnergy (A j) (M j) L (narrowPrimeBand a b H) z)/η < ε/2 := by
    apply (div_lt_iff₀ hη).mpr
    nlinarith
  linarith

#print axioms shiftedPrefixPrimeSkewL1_energy_bound
#print axioms shiftedPrefixPrimeSkewL1_narrow_eventually
end Erdos371.FiniteInformation
