import Submission.HarmonicWordLimit
import Submission.ToeplitzSpectralMeasure

/-! Spectral measures for coordinate observables of a stationary one-sided
finite-alphabet process. The spectral representation is derived from the
proved Toeplitz construction rather than assumed as a library theorem. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
    [MeasurableSpace A] [BorelSpace A]

lemma continuous_word_eval (f : A → ℂ) (k : ℕ) : Continuous (fun x : ℕ → A => f (x k)) :=
  continuous_of_discreteTopology.comp (continuous_apply k)

lemma continuous_word_pair (f : A → ℂ) (i j : ℕ) :
    Continuous (fun x : ℕ → A => f (x i)*conj (f (x j))) :=
  (continuous_word_eval f i).mul (continuous_conj.comp (continuous_word_eval f j))

lemma wordShift_iterate_apply (x : ℕ → A) (m k : ℕ) : (wordShift^[m] x) k = x (m+k) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply,ih]
    change x (m+k+1) = x (m+1+k)
    congr 1
    omega

lemma stationary_word_integral_shift (μ : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (hμ : MeasurePreserving wordShift μ μ) (F : C((ℕ → A),ℂ)) (m : ℕ) :
    (∫ x, F (wordShift^[m] x) ∂μ) = ∫ x, F x ∂μ := by
  rw [← integral_map (hμ.iterate m).measurable.aemeasurable F.continuous.aestronglyMeasurable,
    (hμ.iterate m).map_eq]

noncomputable def wordCovariance (μ : Measure (ℕ → A)) (f : A → ℂ) (k : ℤ) : ℂ :=
  ∫ x, f (x k.toNat)*conj (f (x (-k).toNat)) ∂μ

lemma wordCovariance_hermitian (μ : Measure (ℕ → A)) (f : A → ℂ) (k : ℤ) :
    wordCovariance μ f (-k) = conj (wordCovariance μ f k) := by
  simp only [wordCovariance,neg_neg,← integral_conj,map_mul,starRingEnd_self_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma wordCovariance_pair (μ : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (hμ : MeasurePreserving wordShift μ μ) (f : A → ℂ) (i j : ℕ) :
    wordCovariance μ f ((i : ℤ)-j) = ∫ x, f (x i)*conj (f (x j)) ∂μ := by
  let F : C((ℕ → A),ℂ) :=
    ⟨fun x => f (x ((i : ℤ)-j).toNat)*conj (f (x (-((i : ℤ)-j)).toNat)),
      continuous_word_pair f _ _⟩
  have hh := stationary_word_integral_shift μ hμ F (min i j)
  have he (x : ℕ → A) : F (wordShift^[min i j] x) = f (x i)*conj (f (x j)) := by
    change f ((wordShift^[min i j] x) ((i : ℤ)-j).toNat)*
      conj (f ((wordShift^[min i j] x) (-((i : ℤ)-j)).toNat)) = _
    rw [wordShift_iterate_apply,wordShift_iterate_apply]
    rw [show min i j+((i : ℤ)-j).toNat=i by omega,
      show min i j+(-((i : ℤ)-j)).toNat=j by omega]
  simpa only [he] using hh.symm

lemma wordCovariance_positive (μ : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (hμ : MeasurePreserving wordShift μ μ) (f : A → ℂ) : ToeplitzPositive (wordCovariance μ f) := by
  intro H a
  let S (x : ℕ → A) : ℂ := ∑ i ∈ range H, conj (a i)*f (x i)
  have hc : Continuous S := continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_word_eval f i))
  have hint (i j : ℕ) : Integrable (fun x : ℕ → A => conj (a i)*a j*(f (x i)*conj (f (x j)))) μ :=
    (continuous_const.mul (continuous_word_pair f i j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : ℕ → A) : S x*conj (S x) =
      ∑ i ∈ range H, ∑ j ∈ range H, conj (a i)*a j*(f (x i)*conj (f (x j))) := by
    dsimp only [S]
    simp only [map_sum,map_mul,starRingEnd_self_apply,mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  have heq : (∑ i ∈ range H, ∑ j ∈ range H, conj (a i)*a j*wordCovariance μ f ((i : ℤ)-j)) =
      ∫ x, S x*conj (S x) ∂μ := by
    simp_rw [he]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
    simp_rw [integral_finset_sum _ (fun j _ => hint _ j),integral_const_mul,← wordCovariance_pair μ hμ]
  have hir : Integrable (fun x => S x*conj (S x)) μ :=
    (hc.mul (continuous_conj.comp hc)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [heq]
  change 0 ≤ RCLike.re (∫ x, S x*conj (S x) ∂μ)
  rw [← integral_re hir]
  apply integral_nonneg
  intro x
  change 0 ≤ (S x*conj (S x)).re
  rw [Complex.mul_conj,Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- Every coordinate function in a stationary finite-alphabet process has
a finite positive spectral measure representing all integer covariances. -/
theorem exists_word_spectral_measure (μ : Measure (ℕ → A)) [IsFiniteMeasure μ]
    (hμ : MeasurePreserving wordShift μ μ) (f : A → ℂ) :
    ∃ σ : FiniteMeasure UnitAddCircle, ∀ k : ℤ,
      (∫ x, fourier k x ∂(σ : Measure UnitAddCircle)) = wordCovariance μ f k :=
  exists_toeplitz_spectral_measure (wordCovariance μ f) (wordCovariance_hermitian μ f)
    (wordCovariance_positive μ hμ f)

#print axioms exists_word_spectral_measure
end Erdos371.DilationSpectrum
