import Submission.PrimeFourierImaginaryEnergy
import Submission.HarmonicPrimeLabelSpectrum

/-! Odd prime-shift energies in a stationary word law. All occurrences of
negative gaps are translated to nonnegative coordinates before using the
spectral representation. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

noncomputable def finitePrimeFourierAverage (P : Finset ℕ) (x : UnitAddCircle) : ℂ :=
  (∑ p ∈ P, fourier (p : ℤ) x)/(P.card : ℂ)

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

noncomputable def wordOddAverage (R : ℕ) (P : Finset ℕ) (f : A → ℝ) (x : ℕ → A) : ℝ :=
  (∑ p ∈ P, (f (x (R+p))-f (x (R-p))))/(P.card : ℝ)

lemma continuous_wordOddAverage (R : ℕ) (P : Finset ℕ) (f : A → ℝ) :
    Continuous (wordOddAverage R P f) := by
  apply Continuous.div_const
  apply continuous_finset_sum
  intro p _
  exact ((continuous_of_discreteTopology (f := f)).comp (continuous_apply _)).sub
    ((continuous_of_discreteTopology (f := f)).comp (continuous_apply _))

lemma spectral_word_difference_energy {ι : Type*} [Fintype ι]
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (f : A → ℂ) (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (hσ : ∀ k : ℤ, (∫ x, fourier k x ∂σ) = wordCovariance μ f k)
    (u v : ι → ℕ) :
    (∫ x, ‖∑ i, (fourier (u i : ℤ) x-fourier (v i : ℤ) x)‖^2 ∂σ) =
      ∫ x, ‖∑ i, (f (x (u i))-f (x (v i)))‖^2 ∂μ := by
  let a : ι × Bool → ℂ := fun i => if i.2 then 1 else -1
  let t : ι × Bool → ℕ := fun i => if i.2 then u i.1 else v i.1
  have h := spectral_word_energy μ hμ f σ hσ a t
  simpa only [spectralPolynomial,Fintype.sum_prod_type,Fintype.sum_bool,a,t,
    Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,neg_add_eq_sub] using h

lemma shifted_fourier_odd_sum (R : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R)
    (x : UnitAddCircle) :
    (∑ p ∈ P, (fourier ((R+p : ℕ) : ℤ) x-fourier ((R-p : ℕ) : ℤ) x)) =
      fourier (R : ℤ) x*((∑ p ∈ P, fourier (p : ℤ) x)-conj (∑ p ∈ P, fourier (p : ℤ) x)) := by
  rw [map_sum,← sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro p hp
  simp only [Nat.cast_add,Nat.cast_sub (hP p hp),sub_eq_add_neg,fourier_add,fourier_neg,mul_add,mul_neg]

lemma norm_sub_conj_square (z : ℂ) : ‖z-conj z‖^2 = 4*z.im^2 := by
  have he : z-conj z = (2*z.im : ℝ)*Complex.I := by
    apply Complex.ext <;> simp
    ring
  rw [he,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs,sq_abs]
  ring

lemma wordOddAverage_spectral_energy
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (f : A → ℝ) (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (hσ : ∀ k : ℤ, (∫ x, fourier k x ∂σ) = wordCovariance μ (fun a => (f a : ℂ)) k)
    (R : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p ≤ R) :
    (∫ x, (wordOddAverage R P f x)^2 ∂μ) =
      4*∫ x, ((finitePrimeFourierAverage P x).im)^2 ∂σ := by
  have hs := spectral_word_difference_energy μ hμ (fun a => (f a : ℂ)) σ hσ
    (fun p : P => R+(p : ℕ)) (fun p : P => R-(p : ℕ))
  have hleft (x : UnitAddCircle) :
      (∑ p : P, (fourier ((R+(p : ℕ) : ℕ) : ℤ) x-fourier ((R-(p : ℕ) : ℕ) : ℤ) x)) =
      ∑ p ∈ P, (fourier ((R+p : ℕ) : ℤ) x-fourier ((R-p : ℕ) : ℤ) x) :=
    sum_coe_sort P (fun p => fourier ((R+p : ℕ) : ℤ) x-fourier ((R-p : ℕ) : ℤ) x)
  have hright (x : ℕ → A) :
      (∑ p : P, ((f (x (R+(p : ℕ))) : ℂ)-(f (x (R-(p : ℕ))) : ℂ))) =
        ((∑ p ∈ P, (f (x (R+p))-f (x (R-p)))) : ℝ) := by
    rw [sum_coe_sort P (fun p => (f (x (R+p)) : ℂ)-(f (x (R-p)) : ℂ))]
    simp only [Complex.ofReal_sum,Complex.ofReal_sub]
  simp_rw [hleft,hright,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    shifted_fourier_odd_sum R P hP,norm_mul,fourier_apply,Circle.norm_coe,one_mul,
    norm_sub_conj_square] at hs
  simp only [integral_const_mul] at hs
  unfold wordOddAverage finitePrimeFourierAverage
  simp only [div_pow,integral_div,Complex.div_natCast_im]
  rw [← hs]
  simp only [fourier_apply]
  ring

/-- The L2 odd-shift energy vanishes in every fixed stationary stable-label
law. This is uniform in the translating center R as long as R ≥ N. -/
theorem stationary_wordOddAverage_prime_energy_zero
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ)
    (hdom : ∀ p K : ℕ, 0 < p → ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (f : A → ℝ) (R : ℕ → ℕ) (hR : ∀ N, N ≤ R N) :
    Tendsto (fun N => ∫ x, (wordOddAverage (R N) (initialPrimes N) f x)^2 ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨σ,hσ,hno⟩ := exists_word_spectral_measure_no_infinite_order_atoms μ hμ hdom
    (fun a => (f a : ℂ))
  have ht := (primeFourier_im_square_zero_of_no_infinite_order_atoms
    (σ : Measure UnitAddCircle) hno).const_mul 4
  simp only [mul_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  symm
  exact wordOddAverage_spectral_energy μ hμ f (σ : Measure UnitAddCircle) hσ
    (R N) (initialPrimes N) (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2.trans (hR N))

#print axioms wordOddAverage_spectral_energy
#print axioms stationary_wordOddAverage_prime_energy_zero
end Erdos371.DilationSpectrum
