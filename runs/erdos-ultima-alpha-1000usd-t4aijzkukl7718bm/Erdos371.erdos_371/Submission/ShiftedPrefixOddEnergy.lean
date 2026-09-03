import Submission.ShiftedPrefixEndpointLaw

/-! Odd energies of the global prefix components over a moving harmonic
window have the same limit as the shifted stationary word law. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory DilationSpectrum
open scoped Topology
set_option autoImplicit false

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def shiftedPrefixOddEnergy (A M : ℕ) (L : ℕ → X) (P : Finset ℕ) (b : X) : ℝ :=
  mean (shiftedEndpointLaw A M) (fun i => cyclicOddIndicatorEnergy (shiftedEndpoint A M i)
    (fun x => L x.val) P b)

lemma shiftedPrefixOddEnergy_prefix_error (A M R : ℕ) (L : ℕ → X)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (b : X) :
    |shiftedPrefixOddEnergy A M L P b-shiftedHarmonicMean A M
      (fun k => prefixMean k (fun n => (wordOddAverage R P (labelIndicator b) (wordOrbit L n))^2))| ≤
        32*R/shiftedHarmonicMass A M := by
  rw [← shiftedEndpointLaw_mean]
  unfold shiftedPrefixOddEnergy
  rw [← mean_sub]
  have he := (abs_mean_le_mean_abs (shiftedEndpointLaw A M) _).trans
    (mean_mono _ _ _ (fun i => cyclicOddIndicatorEnergy_prefix_error
      (shiftedEndpoint A M i) R L P hP b))
  have hid : (fun i : Fin (M+1) => 16*(R : ℝ)/(shiftedEndpoint A M i : ℝ)) =
      (fun i => (16*(R : ℝ))*((1 : ℝ)/shiftedEndpoint A M i)) := by funext i; ring
  rw [hid,mean_const_mul] at he
  have hr := mul_le_mul_of_nonneg_left (shiftedEndpointLaw_reciprocal_bound A M)
    (show 0 ≤ 16*(R : ℝ) by positivity)
  exact he.trans (hr.trans_eq (by ring))

variable [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [BorelSpace X]

lemma shiftedPrefixOddEnergy_limit (L : ℕ → X) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (μ : ProbabilityMeasure (ℕ → X))
    (hlim : Tendsto (fun j => shiftedEmpirical (A j) (M j) (wordOrbit L)) atTop (𝓝 μ))
    (R : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (b : X) :
    Tendsto (fun j => shiftedPrefixOddEnergy (A j) (M j) L P b) atTop
      (𝓝 (∫ x, (wordOddAverage R P (labelIndicator b) x)^2 ∂(μ : Measure (ℕ → X)))) := by
  let F : C((ℕ → X),ℝ) := ⟨fun x => (wordOddAverage R P (labelIndicator b) x)^2,
    (continuous_wordOddAverage R P (labelIndicator b)).pow 2⟩
  have hm := shifted_word_integral_tendsto L A M μ hlim F
  have he : Tendsto (fun j => shiftedPrefixOddEnergy (A j) (M j) L P b-
      shiftedHarmonicMean (A j) (M j) (fun n => F (wordOrbit L n))) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => (32*R+24 : ℝ)/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hH
    apply squeeze_zero_norm _ ht
    intro j
    rw [Real.norm_eq_abs]
    have htri := abs_sub_le (shiftedPrefixOddEnergy (A j) (M j) L P b)
      (shiftedHarmonicMean (A j) (M j) (fun k => prefixMean k (fun n => F (wordOrbit L n))))
      (shiftedHarmonicMean (A j) (M j) (fun n => F (wordOrbit L n)))
    have hr := shiftedPrefixOddEnergy_prefix_error (A j) (M j) R L P hP b
    have hb := shiftedHarmonicMean_prefix_error_bounded (fun n => F (wordOrbit L n)) 4 (by norm_num)
      (fun n => wordOddAverage_square_le R P _ (labelIndicator_unit b) (wordOrbit L n)) (A j) (M j)
    rw [abs_sub_comm] at hb
    change |shiftedPrefixOddEnergy (A j) (M j) L P b-
      shiftedHarmonicMean (A j) (M j) (fun k => prefixMean k (fun n => F (wordOrbit L n)))| ≤ _ at hr
    calc
      _ ≤ _ := htri
      _ ≤ 32*R/shiftedHarmonicMass (A j) (M j)+(6*4 : ℝ)/shiftedHarmonicMass (A j) (M j) := add_le_add hr hb
      _ = _ := by ring
  simpa only [sub_add_cancel,zero_add] using he.add hm

#print axioms shiftedPrefixOddEnergy_prefix_error
#print axioms shiftedPrefixOddEnergy_limit
end Erdos371.FiniteInformation
