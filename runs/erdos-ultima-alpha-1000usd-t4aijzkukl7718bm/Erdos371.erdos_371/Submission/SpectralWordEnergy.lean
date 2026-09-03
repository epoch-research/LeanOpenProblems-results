import Submission.StationaryWordCovariance

/-! Finite Fourier-polynomial energies agree with stationary word energies.
Finite-window dilation domination therefore transfers to the spectral side. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma integral_sum_mul_conj {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (a : ι → ℂ) (v : ι → X → ℂ)
    (hv : ∀ i, Continuous (v i)) :
    (∫ x, (∑ i, a i*v i x)*conj (∑ i, a i*v i x) ∂μ) =
      ∑ i, ∑ j, a i*conj (a j)*(∫ x, v i x*conj (v j x) ∂μ) := by
  have hint (i j : ι) : Integrable (fun x => a i*conj (a j)*(v i x*conj (v j x))) μ :=
    (continuous_const.mul ((hv i).mul (continuous_conj.comp (hv j)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : X) : (∑ i, a i*v i x)*conj (∑ i, a i*v i x) =
      ∑ i, ∑ j, a i*conj (a j)*(v i x*conj (v j x)) := by
    simp only [map_sum,map_mul,mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hint _ j),integral_const_mul]

noncomputable def spectralPolynomial {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (t : ι → ℕ) (x : UnitAddCircle) : ℂ := ∑ i, a i*fourier (t i) x

lemma continuous_spectralPolynomial {ι : Type*} [Fintype ι] (a : ι → ℂ) (t : ι → ℕ) :
    Continuous (spectralPolynomial a t) :=
  continuous_finset_sum _ (fun i _ => continuous_const.mul (fourier (t i)).continuous)

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma spectral_word_energy {ι : Type*} [Fintype ι]
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ) (f : A → ℂ)
    (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (hσ : ∀ k : ℤ, (∫ x, fourier k x ∂σ) = wordCovariance μ f k) (a : ι → ℂ) (t : ι → ℕ) :
    (∫ x, ‖spectralPolynomial a t x‖^2 ∂σ) = ∫ x, ‖∑ i, a i*f (x (t i))‖^2 ∂μ := by
  have hc : (∫ x, spectralPolynomial a t x*conj (spectralPolynomial a t x) ∂σ) =
      ∫ x, (∑ i, a i*f (x (t i)))*conj (∑ i, a i*f (x (t i))) ∂μ := by
    unfold spectralPolynomial
    rw [integral_sum_mul_conj σ a (fun i => fourier (t i)) (fun i => (fourier (t i)).continuous),
      integral_sum_mul_conj μ a (fun i x => f (x (t i))) (fun i => continuous_word_eval f (t i))]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    congr 1
    have he (x : UnitAddCircle) : fourier (t i) x*conj (fourier (t j) x) =
        fourier ((t i : ℤ)-t j) x := by rw [← fourier_neg,← fourier_add]; rfl
    simp_rw [he]
    rw [hσ,wordCovariance_pair μ hμ]
  simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq,integral_complex_ofReal] at hc
  exact_mod_cast hc

lemma fourier_nsmul_nat (p n : ℕ) (x : UnitAddCircle) :
    fourier (n : ℤ) (p • x) = fourier ((p*n : ℕ) : ℤ) x := by
  simp only [fourier_apply,Nat.cast_mul,mul_smul,natCast_zsmul]
  rw [smul_comm n p x]

lemma spectralPolynomial_nsmul {ι : Type*} [Fintype ι] (a : ι → ℂ) (t : ι → ℕ)
    (p : ℕ) (x : UnitAddCircle) :
    spectralPolynomial a t (p • x) = spectralPolynomial a (fun i => p*t i) x := by
  simp only [spectralPolynomial,fourier_nsmul_nat]

/-- On a finite alphabet, the unit-bound restriction on a nonnegative
cylinder observable can be removed by one fixed finite normalization. -/
lemma cylinder_dilation_nonnegative (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (p K : ℕ)
    (hdom : ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (F : (Fin K → A) → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ := by
  let B : ℝ := (∑ x : Fin K → A, F x)+1
  have hB : 0 < B := by
    dsimp only [B]
    have hh := sum_nonneg (fun x (_ : x ∈ (univ : Finset (Fin K → A))) => hF x)
    linarith
  have hbound (x : Fin K → A) : F x ≤ B := by
    have hh := single_le_sum (s := (univ : Finset (Fin K → A))) (fun y _ => hF y) (mem_univ x)
    dsimp only [B]
    linarith
  have hd := hdom (fun x => F x/B) (fun x => ⟨div_nonneg (hF x) hB.le,(div_le_one hB).mpr (hbound x)⟩)
  simp only [integral_div] at hd
  have hh := (mul_le_mul_of_nonneg_right hd hB.le)
  have hb : B ≠ 0 := hB.ne'
  field_simp at hh
  exact hh

/-- The spectral energy of an analytic Fourier polynomial is dominated by
p times its dilated energy. This is the exact positivity needed to control
point masses; no uniform prime exponential estimate is hidden here. -/
theorem spectral_polynomial_dilation_bound
    (μ : Measure (ℕ → A)) [IsFiniteMeasure μ] (hμ : MeasurePreserving wordShift μ μ) (f : A → ℂ)
    (σ : Measure UnitAddCircle) [IsFiniteMeasure σ]
    (hσ : ∀ k : ℤ, (∫ x, fourier k x ∂σ) = wordCovariance μ f k)
    (p K : ℕ)
    (hdom : ∀ F : (Fin K → A) → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
      (∫ x, F (fun k => x k) ∂μ) ≤ p*∫ x, F (fun k => x (p*k)) ∂μ)
    (a : Fin K → ℂ) :
    (∫ x, ‖spectralPolynomial a (fun k => k) x‖^2 ∂σ) ≤
      p*∫ x, ‖spectralPolynomial a (fun k => k) (p • x)‖^2 ∂σ := by
  simp_rw [spectralPolynomial_nsmul]
  rw [spectral_word_energy μ hμ f σ hσ a (fun k => k),
    spectral_word_energy μ hμ f σ hσ a (fun k => p*k)]
  exact cylinder_dilation_nonnegative μ p K hdom
    (fun x => ‖∑ k, a k*f (x k)‖^2) (fun _ => sq_nonneg _)

#print axioms spectral_polynomial_dilation_bound
end Erdos371.DilationSpectrum
