import Submission.CyclicWordBoundary

/-! The componentwise cyclic odd energies converge to the energies of the
common stationary harmonic word law. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory DilationSpectrum
open scoped Topology
set_option autoImplicit false

instance harmonicPrefixLength_neZero (N : ℕ) (i : Fin (N+1)) :
    NeZero (harmonicPrefixLength N i) := ⟨(harmonicPrefixLength_pos N i).ne'⟩

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def harmonicPrefixOddEnergy (N : ℕ) (L : ℕ → A) (P : Finset ℕ) (b : A) : ℝ :=
  mean (harmonicPrefixLaw N) (fun i => cyclicOddIndicatorEnergy (harmonicPrefixLength N i)
    (fun x => L x.val) P b)

lemma harmonicPrefixOddEnergy_range_error (N R : ℕ) (L : ℕ → A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (b : A) :
    |harmonicPrefixOddEnergy N L P b-harmonicRangeMean (N+1)
      (fun n => (wordOddAverage R P (labelIndicator b) (wordOrbit L n))^2)| ≤
        16*R/(harmonic (N+1) : ℝ) := by
  unfold harmonicPrefixOddEnergy harmonicRangeMean
  rw [← harmonicPrefixLaw_representation,← mean_sub]
  apply (abs_mean_le_mean_abs _ _).trans
  apply (mean_mono _ _ _ (fun i => cyclicOddIndicatorEnergy_prefix_error
    (harmonicPrefixLength N i) R L P hP b)).trans_eq
  have he : (fun i : Fin (N+1) => 16*(R : ℝ)/(harmonicPrefixLength N i : ℝ)) =
      (fun i => (16*(R : ℝ))*((1 : ℝ)/harmonicPrefixLength N i)) := by funext i; ring
  rw [he,mean_const_mul,harmonicPrefixLaw_reciprocal_length]
  ring

lemma harmonicMean_range_error_bounded (N : ℕ) (F : ℕ → ℝ)
    (B : ℝ) (hB : 0 < B) (hF : ∀ n, |F n| ≤ B) :
    |harmonicRangeMean (N+1) F-harmonicMean (N+1) F| ≤ 2*B/(harmonic (N+1) : ℝ) := by
  have h := harmonicMean_range_error N (fun n => B⁻¹*F n) (fun n => by
    rw [abs_mul,abs_of_pos (inv_pos.mpr hB)]
    have hh := mul_le_mul_of_nonneg_left (hF n) (inv_nonneg.mpr hB.le)
    simpa only [inv_mul_cancel₀ hB.ne'] using hh)
  rw [harmonicRangeMean_const_mul,harmonicMean_const_mul,← mul_sub,abs_mul,
    abs_of_pos (inv_pos.mpr hB)] at h
  have hh := mul_le_mul_of_nonneg_left h hB.le
  calc
    _ = B*(B⁻¹*|harmonicRangeMean (N+1) F-harmonicMean (N+1) F|) := by
      rw [← mul_assoc,mul_inv_cancel₀ hB.ne',one_mul]
    _ ≤ _ := hh
    _ = _ := by ring

variable [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

lemma harmonicPrefixOddEnergy_limit (L : ℕ → A) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (R : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (b : A) :
    Tendsto (fun j => harmonicPrefixOddEnergy (D j) L P b) atTop
      (𝓝 (∫ x, (wordOddAverage R P (labelIndicator b) x)^2 ∂(μ : Measure (ℕ → A)))) := by
  let F : C((ℕ → A),ℝ) := ⟨fun x => (wordOddAverage R P (labelIndicator b) x)^2,
    (continuous_wordOddAverage R P (labelIndicator b)).pow 2⟩
  have hm := harmonic_word_integral_tendsto L D μ hlim F
  have he : Tendsto (fun j => harmonicPrefixOddEnergy (D j) L P b-
      harmonicMean (D j+1) (fun n => F (wordOrbit L n))) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => (16*R+8 : ℝ)/(harmonic (D j+1) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (harmonic_real_tendsto.comp hD)
    apply squeeze_zero_norm _ ht
    intro j
    rw [Real.norm_eq_abs]
    have htri := abs_sub_le (harmonicPrefixOddEnergy (D j) L P b)
      (harmonicRangeMean (D j+1) (fun n => F (wordOrbit L n)))
      (harmonicMean (D j+1) (fun n => F (wordOrbit L n)))
    have hr := harmonicPrefixOddEnergy_range_error (D j) R L P hP b
    have hb := harmonicMean_range_error_bounded (D j) (fun n => F (wordOrbit L n)) 4 (by norm_num)
      (fun n => wordOddAverage_square_le R P _ (labelIndicator_unit b) (wordOrbit L n))
    change |harmonicPrefixOddEnergy (D j) L P b-
      harmonicRangeMean (D j+1) (fun n => F (wordOrbit L n))| ≤ _ at hr
    calc
      _ ≤ _ := htri
      _ ≤ 16*R/(harmonic (D j+1) : ℝ)+(2*4 : ℝ)/(harmonic (D j+1) : ℝ) := add_le_add hr hb
      _ = _ := by ring
  simpa only [sub_add_cancel,zero_add] using he.add hm

#print axioms harmonicPrefixOddEnergy_range_error
#print axioms harmonicPrefixOddEnergy_limit
end Erdos371.FiniteInformation
