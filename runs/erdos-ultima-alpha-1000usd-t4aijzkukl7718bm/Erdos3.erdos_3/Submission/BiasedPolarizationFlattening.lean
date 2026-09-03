import Submission.BiasedPhaseSpectrum

/-! Bias converts approximate constancy of a phase derivative into a bound
on its value. This is the final analytic step for polarization-based local
flattening; domain and spectral hypotheses remain explicit. -/
namespace Erdos3BiasedPolarizationFlattening
open Finset Erdos3BiasedPhaseSpectrum Erdos3LocalQuadraticPolarization
  Erdos3LocalQuadraticProgressions Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- If a biased phase has derivative approximately equal to a constant c,
then c is close to one, at the cost of dividing by the bias. -/
theorem biased_constant_derivative (C : Finset G) (hC : C.Nonempty)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (h : G) (c : ℂ)
    {β a b : ℝ} (hβ : 0 < β) (hbias : β ≤ ‖𝔼 x : C, q x‖)
    (happrox : ∀ x ∈ C, ‖derivative q h x-c‖ ≤ a)
    (hstable : (𝔼 x : G, |normalized C (x+h)-normalized C x|) ≤ b) :
    ‖c-1‖ ≤ (a+b)/β := by
  letI : Nonempty C := hC.to_subtype
  have he (x : G) : q (x+h)-c*q x = (derivative q h x-c)*q x := by
    have ht : q (x+h) = derivative q h x*q x :=
      unit_conj_cancel (hq x) (show q (x+h)*conj (q x) = derivative q h x from rfl)
    rw [ht]
    ring
  have hmean : ‖(𝔼 x : C, q (x+h))-c*(𝔼 x : C, q x)‖ ≤ a := by
    rw [mul_expect,← expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    rw [he,norm_mul,hq,mul_one]
    exact happrox x x.property
  have ht := (window_mean_translation C hC q (fun x ↦ (hq x).le) h).trans hstable
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (c*(𝔼 x : C, q x)) (𝔼 x : C, q (x+h)) (𝔼 x : C, q x)
  rw [norm_sub_rev (c*(𝔼 x : C, q x)) (𝔼 x : C, q (x+h))] at htri
  have hid : c*(𝔼 x : C, q x)-(𝔼 x : C, q x) = (c-1)*(𝔼 x : C, q x) := by ring
  rw [hid,norm_mul] at htri
  have hb := mul_le_mul_of_nonneg_left hbias (norm_nonneg (c-1))
  apply (le_div_iff₀ hβ).mpr
  nlinarith

/-- Bias and small polarization control the phase at the base point. -/
theorem biased_polarization_flattening (C : Finset G) (hC : C.Nonempty)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (y : G)
    {β a b : ℝ} (hβ : 0 < β) (hbias : β ≤ ‖𝔼 x : C, q x‖)
    (hpolar : ∀ x ∈ C, ‖localPolar q x y-1‖ ≤ a)
    (hstable : (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ b) :
    ‖q y-q 0‖ ≤ (a+b)/β ∧
      ∀ x ∈ C, ‖q (x+y)-q x‖ ≤ a+(a+b)/β := by
  have hder (x : G) (hx : x ∈ C) : ‖derivative q y x-derivative q y 0‖ ≤ a := by
    have he : derivative q y x-derivative q y 0 =
        derivative q y 0*(localPolar q y x-1) := by
      rw [derivative_eq_localPolar q hq y x]
      ring
    rw [he,norm_mul,derivative_norm_one q hq,one_mul,localPolar_symmetric]
    exact hpolar x hx
  have hflat := biased_constant_derivative C hC q hq y (derivative q y 0)
    hβ hbias hder hstable
  have he (x : G) : ‖q (x+y)-q x‖ = ‖derivative q y x-1‖ := by
    have hid : q (x+y)-q x = (derivative q y x-1)*q x := by
      have ht := unit_conj_cancel (hq x)
        (show q (x+y)*conj (q x) = derivative q y x from rfl)
      rw [ht]
      ring
    rw [hid,norm_mul,hq,mul_one]
  refine ⟨?_,?_⟩
  · simpa only [zero_add] using (he 0).trans_le hflat
  · intro x hx
    rw [he]
    exact (norm_sub_le_norm_sub_add_norm_sub (derivative q y x) (derivative q y 0) 1).trans
      (add_le_add (hder x hx) hflat)

#print axioms biased_constant_derivative
#print axioms biased_polarization_flattening
end Erdos3BiasedPolarizationFlattening
