import Submission.HarmonicPrefixOddEnergy
import Submission.NarrowPrimeBandEnergy

/-! Prime-gap skew cancellation in the L1 harmonic mixture of ordinary
prefixes. A single common stationary word law controls all component tests. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory DilationSpectrum AbelPrimes
open scoped Topology
set_option autoImplicit false

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def naturalPrimeSkewAverage (N : ℕ) (L : ℕ → A)
    (P : Finset ℕ) (C : A → A → ℝ) : ℝ :=
  (∑ p ∈ P, prefixMean N (fun n => C (L n) (L (n+p))))/(P.card : ℝ)

noncomputable def harmonicPrefixPrimeSkewL1 (N : ℕ) (L : ℕ → A)
    (P : Finset ℕ) (C : Fin (N+1) → A → A → ℝ) : ℝ :=
  mean (harmonicPrefixLaw N) (fun i => |naturalPrimeSkewAverage (harmonicPrefixLength N i) L P (C i)|)

lemma cyclicSkew_wordMean (N : ℕ) [NeZero N] (L : ZMod N → A)
    (C : A → A → ℝ) (p : ℕ) :
    cyclicSkew L C (p : ZMod N) = cyclicWordMean N L (fun x => C (x 0) (x p)) := by
  unfold cyclicWordMean cyclicWordOrbit
  simp only [Nat.cast_zero,add_zero]
  exact (mean_uniform_eq_cyclicSkew N L C (p : ZMod N)).symm

lemma naturalPrimeSkewAverage_cyclic_error (N R : ℕ) [NeZero N] (L : ℕ → A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |naturalPrimeSkewAverage N L P C-cyclicPrimeSkewAverage N (fun x => L x.val) P C| ≤ 2*R/N := by
  by_cases hne : P.Nonempty
  · unfold naturalPrimeSkewAverage cyclicPrimeSkewAverage
    rw [← sub_div,← sum_sub_distrib]
    apply abs_finset_average_le P hne
    intro p hp
    rw [cyclicSkew_wordMean,abs_sub_comm]
    have hh := cyclicWordMean_prefix_error N p L (fun x => C (x 0) (x p)) 1 (by norm_num)
      (fun x => hC _ _) (fun x y hxy => by dsimp only; rw [hxy 0 (Nat.zero_le p),hxy p le_rfl])
    simp only [wordOrbit,Nat.add_zero,mul_one] at hh
    exact hh.trans (div_le_div_of_nonneg_right (by exact_mod_cast (show 2*p ≤ 2*R from Nat.mul_le_mul_left 2 (hP p hp)))
      (Nat.cast_nonneg N))
  · simp only [naturalPrimeSkewAverage,cyclicPrimeSkewAverage,not_nonempty_iff_eq_empty.mp hne,
      sum_empty,card_empty,Nat.cast_zero,div_zero,sub_self,abs_zero]
    positivity

lemma harmonicPrefixPrimeSkewL1_energy_bound (N R : ℕ) (L : ℕ → A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) (C : Fin (N+1) → A → A → ℝ)
    (hC : ∀ i a b, C i b a = -C i a b) (hCb : ∀ i a b, |C i a b| ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    2*harmonicPrefixPrimeSkewL1 N L P C ≤ Fintype.card A*η+
      (∑ b, harmonicPrefixOddEnergy N L P b)/η+4*R/(harmonic (N+1) : ℝ) := by
  have hcyc := componentwise_cyclicPrimeSkewAverage_energy_bound (harmonicPrefixLength N)
    (harmonicPrefixLaw N) (fun _ x => L x.val) P C hC hCb η hη
  rw [mean_finset_sum] at hcyc
  change 2*mean (harmonicPrefixLaw N) (fun i =>
    |cyclicPrimeSkewAverage (harmonicPrefixLength N i) (fun x => L x.val) P (C i)|) ≤
      Fintype.card A*η+(∑ b, harmonicPrefixOddEnergy N L P b)/η at hcyc
  have hcomp (i : Fin (N+1)) : |naturalPrimeSkewAverage (harmonicPrefixLength N i) L P (C i)| ≤
      |cyclicPrimeSkewAverage (harmonicPrefixLength N i) (fun x => L x.val) P (C i)|+
        2*R/(harmonicPrefixLength N i : ℝ) := by
    have he := naturalPrimeSkewAverage_cyclic_error (harmonicPrefixLength N i) R L P hP (C i) (hCb i)
    have ht := abs_sub_le (naturalPrimeSkewAverage (harmonicPrefixLength N i) L P (C i))
      (cyclicPrimeSkewAverage (harmonicPrefixLength N i) (fun x => L x.val) P (C i)) 0
    simp only [sub_zero] at ht
    linarith
  have hm := mean_mono (harmonicPrefixLaw N) _ _ hcomp
  rw [mean_add] at hm
  have he : (fun i : Fin (N+1) => 2*(R : ℝ)/(harmonicPrefixLength N i : ℝ)) =
      (fun i => (2*(R : ℝ))*((1 : ℝ)/harmonicPrefixLength N i)) := by funext i; ring
  rw [he,mean_const_mul,harmonicPrefixLaw_reciprocal_length] at hm
  change harmonicPrefixPrimeSkewL1 N L P C ≤ _ at hm
  simp only [mul_one_div] at hm
  rw [show 4*(R : ℝ)/(harmonic (N+1) : ℝ) = 2*(2*(R : ℝ)/(harmonic (N+1) : ℝ)) by ring]
  linarith

variable [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]

/-- Choose the large prime-band starting scale using the common word law.
For each subsequent FIXED band scale, the entire L1 mixture is eventually
small, uniformly over all bounded skew component observables. -/
theorem harmonicPrefixPrimeSkewL1_narrow_eventually
    (L : ℕ → A) (D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (μ : ProbabilityMeasure (ℕ → A))
    (hlim : Tendsto (fun j => harmonicEmpirical (D j) (wordOrbit L)) atTop (𝓝 μ))
    (hμ : MeasurePreserving wordShift (μ : Measure (ℕ → A)) (μ : Measure (ℕ → A)))
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂(μ : Measure (ℕ → A))) ≤
        p*∫ x, F (fun k => x (p*k)) ∂(μ : Measure (ℕ → A)))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ᶠ j : ℕ in atTop,
      ∀ C : Fin (D j+1) → A → A → ℝ,
        (∀ i x y, C i y x = -C i x y) → (∀ i x y, |C i x y| ≤ 1) →
          harmonicPrefixPrimeSkewL1 (D j) L (narrowPrimeBand a b H) C < ε := by
  let η : ℝ := ε/(4*(Fintype.card A+1 : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hcoef : (Fintype.card A : ℝ)*η < ε/4 := by
    have he : η*(4*(Fintype.card A+1 : ℝ))=ε := by dsimp [η]; field_simp
    nlinarith
  let E (H : ℕ) : ℝ := ∑ z : A, ∫ x, (wordOddAverage (linearPrimeEndpoint b H)
    (narrowPrimeBand a b H) (labelIndicator z) x)^2 ∂(μ : Measure (ℕ → A))
  have hE : Tendsto E atTop (𝓝 0) := by
    have ht := tendsto_finset_sum (univ : Finset A) (fun z _ =>
      stationary_wordOddAverage_narrow_prime_energy_zero (μ : Measure (ℕ → A)) hμ hdom
        (labelIndicator z) a b ha hab)
    simpa only [sum_const_zero] using ht
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp
    (hE.eventually_lt_const (by positivity : (0 : ℝ)<η*ε/4))
  refine ⟨H₀,?_⟩
  intro H hH
  have hlimE : Tendsto (fun j => ∑ z, harmonicPrefixOddEnergy (D j) L (narrowPrimeBand a b H) z)
      atTop (𝓝 (E H)) := by
    exact tendsto_finset_sum (univ : Finset A) (fun z _ => harmonicPrefixOddEnergy_limit L D hD μ hlim
      (linearPrimeEndpoint b H) (narrowPrimeBand a b H)
      (fun p hp => (narrowPrimeBand_member_bounds a b H p hp).2) z)
  have hsmallE := hlimE.eventually_lt_const
    (show E H < η*ε/2 by have hh := hH₀ H hH; nlinarith)
  have ht : Tendsto (fun j => 4*(linearPrimeEndpoint b H : ℝ)/(harmonic (D j+1) : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (harmonic_real_tendsto.comp hD)
  filter_upwards [hsmallE,ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with j hj htail
  intro C hC hCb
  have hb := harmonicPrefixPrimeSkewL1_energy_bound (D j) (linearPrimeEndpoint b H) L
    (narrowPrimeBand a b H) (fun p hp => (narrowPrimeBand_member_bounds a b H p hp).2) C hC hCb η hη
  have hdiv : (∑ z, harmonicPrefixOddEnergy (D j) L (narrowPrimeBand a b H) z)/η < ε/2 := by
    apply (div_lt_iff₀ hη).mpr
    nlinarith
  linarith

#print axioms harmonicPrefixPrimeSkewL1_energy_bound
#print axioms harmonicPrefixPrimeSkewL1_narrow_eventually
end Erdos371.FiniteInformation
