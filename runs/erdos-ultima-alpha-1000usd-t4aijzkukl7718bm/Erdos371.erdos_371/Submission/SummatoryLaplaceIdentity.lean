import Submission.LogarithmicSummatory

/-! The Fourier--Laplace transform of the logarithmically reparametrized
summatory function, derived from Mathlib's Dirichlet-series integral formula
by the exponential change of variables. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform Finset
open scoped Topology
set_option autoImplicit false

noncomputable def laplacePoint (σ ξ : ℝ) : ℂ := (σ : ℂ)+(2*Real.pi*ξ : ℝ)*Complex.I

lemma laplacePoint_re (σ ξ : ℝ) : (laplacePoint σ ξ).re = σ := by simp [laplacePoint]

lemma damped_fourier_integrand (f : ℝ → ℂ) (σ ξ t : ℝ) :
    Complex.exp (↑(-2*Real.pi*t*ξ)*Complex.I)*damped f σ t =
      Complex.exp (-laplacePoint σ ξ*t)*f t := by
  simp only [damped,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2
  simp only [laplacePoint,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  ring

lemma fourier_damped_halfLine (f : ℝ → ℂ) (hsupp : ∀ t, t < 0 → f t = 0) (σ ξ : ℝ) :
    𝓕 (damped f σ) ξ = ∫ t : ℝ in Set.Ioi 0, Complex.exp (-laplacePoint σ ξ*t)*f t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,damped_fourier_integrand]
  rw [← integral_Ici_eq_integral_Ioi,← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  by_cases ht : 0 ≤ t
  · simp only [Set.indicator_of_mem (show t ∈ Set.Ici (0 : ℝ) from ht)]
  · simp [Set.indicator_of_notMem (show t ∉ Set.Ici (0 : ℝ) from ht),hsupp t (by linarith)]

lemma exp_image_positive : Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi 1 := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    simpa using Real.exp_lt_exp.mpr ht
  · intro hx
    have hx' : (1 : ℝ) < x := hx
    refine ⟨Real.log x,Real.log_pos hx,Real.exp_log (by linarith)⟩

lemma real_exp_cpow (t : ℝ) (s : ℂ) : (Real.exp t : ℂ)^s = Complex.exp ((t : ℂ)*s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le,Real.log_exp]

lemma exp_mellin_integrand (a : ℕ → ℝ) (s : ℂ) (t : ℝ) :
    |Real.exp t| • ((summatory a (Real.exp t) : ℂ)*(Real.exp t : ℂ)^(-(s+1))) =
      Complex.exp (-s*t)*(summatory a (Real.exp t) : ℂ) := by
  rw [abs_of_pos (Real.exp_pos t),Complex.real_smul,real_exp_cpow]
  simp only [Complex.ofReal_exp]
  calc
    _ = (Complex.exp (t : ℂ)*Complex.exp ((t : ℂ)*(-(s+1))))*
        (summatory a (Real.exp t) : ℂ) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

lemma expSummatory_laplace_integrand (a : ℕ → ℝ) (z : ℂ) (t : ℝ) :
    Complex.exp (-z*t)*(expSummatory a t : ℂ) =
      Complex.exp (-(1+z)*t)*(summatory a (Real.exp t) : ℂ) := by
  simp only [expSummatory,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,
    ← mul_assoc,← Complex.exp_add]
  congr 2
  ring

lemma LSeries_expSummatory_fourier (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N)
    (σ ξ : ℝ) (hσ : 0 < σ) :
    LSeries (fun n => (a n : ℂ)) (1+laplacePoint σ ξ) =
      (1+laplacePoint σ ξ)*𝓕 (damped (fun t => (expSummatory a t : ℂ)) σ) ξ := by
  let s := 1+laplacePoint σ ξ
  have hs : 1 < s.re := by simp only [s,Complex.add_re,Complex.one_re,laplacePoint_re]; linarith
  have hL := LSeries_eq_mul_integral_of_nonneg a zero_le_one hs (summatory_bigO a ha C hC hbound) ha
  change LSeries (fun n => (a n : ℂ)) s = s*_ 
  rw [hL,fourier_damped_halfLine _ (fun t ht => by simp only [expSummatory_zero_of_neg a t ht,Complex.ofReal_zero])]
  congr 1
  let g := fun x : ℝ => (summatory a x : ℂ)*(x : ℂ)^(-(s+1))
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ht : t ∈ Set.Ioi (0 : ℝ)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [exp_image_positive] at hi
  simp only [g,exp_mellin_integrand] at hi
  simp_rw [expSummatory_laplace_integrand]
  convert hi using 1
  simp only [summatory,Complex.ofReal_sum]

lemma fourier_damped_halfLineUnit (σ ξ : ℝ) (hσ : 0 < σ) :
    𝓕 (damped (fun t => (halfLineUnit t : ℂ)) σ) ξ = (laplacePoint σ ξ)⁻¹ := by
  rw [fourier_damped_halfLine _ (fun t ht => by simp [halfLineUnit,not_le.mpr ht])]
  have he : (∫ t : ℝ in Set.Ioi 0, Complex.exp (-laplacePoint σ ξ*t)*(halfLineUnit t : ℂ)) =
      ∫ t : ℝ in Set.Ioi 0, Complex.exp (-laplacePoint σ ξ*t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp [halfLineUnit,(show (0 : ℝ) < t from ht).le]
  rw [he,integral_exp_mul_complex_Ioi (by simp only [Complex.neg_re,laplacePoint_re]; linarith) 0]
  simp

#print axioms LSeries_expSummatory_fourier
end Erdos371.FourierBoundary
