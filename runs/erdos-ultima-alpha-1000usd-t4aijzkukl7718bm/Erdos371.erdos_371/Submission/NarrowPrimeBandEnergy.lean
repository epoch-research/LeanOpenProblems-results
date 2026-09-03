import Submission.NarrowPrimeBands

/-! The fixed relative-width bands have vanishing imaginary Fourier energy
for every fixed spectral measure with no infinite-order atoms. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma continuous_finitePrimeFourierAverage (P : Finset ℕ) : Continuous (finitePrimeFourierAverage P) :=
  (continuous_finset_sum P (fun p _ => (fourier (p : ℤ)).continuous)).div_const _

lemma card_mul_finitePrimeFourierAverage (P : Finset ℕ) (x : UnitAddCircle) :
    (P.card : ℂ)*finitePrimeFourierAverage P x = ∑ p ∈ P, fourier (p : ℤ) x := by
  by_cases hP : P.Nonempty
  · have hc : (P.card : ℂ) ≠ 0 := by exact_mod_cast (card_pos.mpr hP).ne'
    unfold finitePrimeFourierAverage
    field_simp
  · have he : P = ∅ := not_nonempty_iff_eq_empty.mp hP
    simp [he,finitePrimeFourierAverage]

lemma finitePrimeFourierAverage_sdiff_im (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hne : (P \ Q).Nonempty) (x : UnitAddCircle) :
    (finitePrimeFourierAverage (P \ Q) x).im =
      ((P.card : ℝ)/(P \ Q).card)*(finitePrimeFourierAverage P x).im-
        ((Q.card : ℝ)/(P \ Q).card)*(finitePrimeFourierAverage Q x).im := by
  have he : ((P \ Q).card : ℂ)*finitePrimeFourierAverage (P \ Q) x =
      (P.card : ℂ)*finitePrimeFourierAverage P x-(Q.card : ℂ)*finitePrimeFourierAverage Q x := by
    simp only [card_mul_finitePrimeFourierAverage]
    exact sum_sdiff_eq_sub hQP
  have hi := congrArg Complex.im he
  simp only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero,Complex.sub_im] at hi
  have hc : ((P \ Q).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
  field_simp
  nlinarith

lemma finitePrimeFourierAverage_sdiff_energy (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hne : (P \ Q).Nonempty) (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] :
    (∫ x, ((finitePrimeFourierAverage (P \ Q) x).im)^2 ∂μ) ≤
      2*((P.card : ℝ)/(P \ Q).card)^2*(∫ x, ((finitePrimeFourierAverage P x).im)^2 ∂μ)+
      2*((Q.card : ℝ)/(P \ Q).card)^2*(∫ x, ((finitePrimeFourierAverage Q x).im)^2 ∂μ) := by
  have hint (S : Finset ℕ) : Integrable (fun x => ((finitePrimeFourierAverage S x).im)^2) μ :=
    ((Complex.continuous_im.comp (continuous_finitePrimeFourierAverage S)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (x : UnitAddCircle) : ((finitePrimeFourierAverage (P \ Q) x).im)^2 ≤
      2*((P.card : ℝ)/(P \ Q).card)^2*((finitePrimeFourierAverage P x).im)^2+
      2*((Q.card : ℝ)/(P \ Q).card)^2*((finitePrimeFourierAverage Q x).im)^2 := by
    rw [finitePrimeFourierAverage_sdiff_im P Q hQP hne]
    nlinarith [sq_nonneg (((P.card : ℝ)/(P \ Q).card)*(finitePrimeFourierAverage P x).im+
      ((Q.card : ℝ)/(P \ Q).card)*(finitePrimeFourierAverage Q x).im)]
  have h := integral_mono (hint _) (((hint P).const_mul _).add ((hint Q).const_mul _)) hpoint
  simp only [Pi.add_apply] at h
  simpa only [integral_add ((hint P).const_mul _) ((hint Q).const_mul _),integral_const_mul] using h

lemma narrowPrimeBand_count_ratio (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((initialPrimes (linearPrimeEndpoint t N)).card : ℝ)/
      (narrowPrimeBand a b N).card) atTop (𝓝 (t/(b-a))) := by
  have hnum := prime_count_at_linear_endpoint (linearPrimeEndpoint t) (linearPrimeEndpoint_tendsto t ht)
    t ht (linearPrimeEndpoint_ratio t ht.le)
  have hden := narrowPrimeBand_card_scaled_limit a b ha hab
  have hlim := hnum.div hden (sub_ne_zero.mpr hab.ne')
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hn,mul_div_mul_right _ _ hlog]

lemma narrowPrimeBand_eventually_nonempty (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, (narrowPrimeBand a b N).Nonempty := by
  filter_upwards [narrowPrimeBand_eventual_count_lower a b ha hab,eventually_ge_atTop (2 : ℕ)] with N hN hN2
  apply card_pos.mp
  have hp : 0 < ((b-a)/2)*(N : ℝ)/Real.log N := by
    apply div_pos (mul_pos (by linarith) (by exact_mod_cast (show 0 < N by omega)))
    exact Real.log_pos (by exact_mod_cast hN2)
  exact_mod_cast hp.trans_le hN

theorem narrowPrimeBand_im_square_zero (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (hno : ∀ x : UnitAddCircle, ¬IsOfFinAddOrder x → μ {x}=0) :
    Tendsto (fun N => ∫ x, ((finitePrimeFourierAverage (narrowPrimeBand a b N) x).im)^2 ∂μ)
      atTop (𝓝 0) := by
  have hE := primeFourier_im_square_zero_of_no_infinite_order_atoms μ hno
  have hu := ((narrowPrimeBand_count_ratio a b b ha hab (ha.trans hab)).pow 2 |>.const_mul 2).mul
    (hE.comp (linearPrimeEndpoint_tendsto b (ha.trans hab)))
  have hl := ((narrowPrimeBand_count_ratio a b a ha hab ha).pow 2 |>.const_mul 2).mul
    (hE.comp (linearPrimeEndpoint_tendsto a ha))
  have ht := hu.add hl
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) _ ht
  filter_upwards [narrowPrimeBand_eventually_nonempty a b ha hab] with N hN
  exact finitePrimeFourierAverage_sdiff_energy _ _
    (initialPrimes_mono (linearPrimeEndpoint_mono hab.le N)) hN μ

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

theorem stationary_wordOddAverage_narrow_prime_energy_zero
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (f : A → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N => ∫ x, (wordOddAverage (linearPrimeEndpoint b N)
      (narrowPrimeBand a b N) f x)^2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨σ,hσ,hno⟩ := exists_word_spectral_measure_no_infinite_order_atoms μ hμ hdom
    (fun a => (f a : ℂ))
  have ht := (narrowPrimeBand_im_square_zero a b ha hab (σ : Measure UnitAddCircle) hno).const_mul 4
  simp only [mul_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  symm
  exact wordOddAverage_spectral_energy μ hμ f (σ : Measure UnitAddCircle) hσ _ _
    (fun p hp => (narrowPrimeBand_member_bounds a b N p hp).2)

#print axioms narrowPrimeBand_im_square_zero
#print axioms stationary_wordOddAverage_narrow_prime_energy_zero
end Erdos371.DilationSpectrum
