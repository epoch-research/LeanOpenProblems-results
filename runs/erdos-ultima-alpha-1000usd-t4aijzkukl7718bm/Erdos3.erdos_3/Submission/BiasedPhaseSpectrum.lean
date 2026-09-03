import Submission.WeightedSpectrumPacking
import Submission.BohrDerivativeCharacters
import Submission.FixedCenterQuadraticAverage

/-! A biased unit phase whose derivatives admit approximate character
representations forces those characters into one weighted large spectrum.
Relative spectral packing then controls their phases at bounded rank. -/
namespace Erdos3BiasedPhaseSpectrum
open Finset Erdos3WeightedSpectrumPacking Erdos3BohrDerivativeCharacters
  Erdos3FixedCenterQuadraticAverage Erdos3LocalQuadraticPolarization
  Erdos3LocalQuadraticProgressions Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3RelativeSpectrumPhase Erdos3CorrelationSifting Erdos3FiniteBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma window_mean_translation (C : Finset G) (hC : C.Nonempty)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (h : G) :
    ‖(𝔼 x : C, f (x+h))-(𝔼 x : C, f x)‖ ≤
      𝔼 x : G, |normalized C (x+h)-normalized C x| := by
  have he : (𝔼 x : G, (normalized C (x+h) : ℂ)*f (x+h)) = 𝔼 x : C, f x := by
    rw [← expect_normalized_mul_complex C hC f]
    exact Fintype.expect_equiv (Equiv.addRight h) _ _ (fun _ ↦ rfl)
  have ht := weighted_translation_bound_complex (normalized C) (fun x ↦ f (x+h)) (fun x ↦ hf _) h
  rw [he,expect_normalized_mul_complex C hC] at ht
  simpa only [norm_sub_rev] using ht

/-- Derivative approximation and window stability transfer the original bias
to a weighted Fourier coefficient. -/
theorem biased_derivative_coefficient (C : Finset G) (hC : C.Nonempty)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (h : G) (c : ℂ) (hc : ‖c‖ = 1)
    (χ : AddChar G ℂ) {β a b : ℝ}
    (hbias : β ≤ ‖𝔼 x : C, q x‖)
    (happrox : ∀ x ∈ C, ‖derivative q h x-c*χ x‖ ≤ a)
    (hstable : (𝔼 x : G, |normalized C (x+h)-normalized C x|) ≤ b) :
    β-a-b ≤ ‖weightedCoefficient C q χ‖ := by
  letI : Nonempty C := hC.to_subtype
  have he (x : G) : q (x+h)-c*(q x*χ x) =
      (derivative q h x-c*χ x)*q x := by
    have ht : q (x+h) = derivative q h x*q x :=
      unit_conj_cancel (hq x) (show q (x+h)*conj (q x) = derivative q h x from rfl)
    rw [ht]
    ring
  have hmean : ‖(𝔼 x : C, q (x+h))-c*weightedCoefficient C q χ‖ ≤ a := by
    unfold weightedCoefficient
    rw [mul_expect,← expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply expect_le univ_nonempty
    intro x _
    rw [he,norm_mul,hq,mul_one]
    exact happrox x x.property
  have ht := (window_mean_translation C hC q (fun x ↦ (hq x).le) h).trans hstable
  have htri := norm_sub_le_norm_sub_add_norm_sub (𝔼 x : C, q x) (𝔼 x : C, q (x+h)) (c*weightedCoefficient C q χ)
  rw [norm_sub_rev (𝔼 x : C, q x) (𝔼 x : C, q (x+h))] at htri
  have hnorm := norm_sub_norm_le (𝔼 x : C, q x) (c*weightedCoefficient C q χ)
  rw [norm_mul,hc,one_mul] at hnorm
  linarith

/-- A bounded-rank family controls all derivative characters at once.
The bound is independent of the number of derivatives in H. -/
theorem biased_derivative_spectrum_control (C H : Finset G) (hC : C.Nonempty)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (F : G → AddChar G ℂ)
    (c : G → ℂ) (hc : ∀ h ∈ H, ‖c h‖ = 1)
    {β a b η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (herr : ε ≤ η^2/2) (hbudget : η ≤ β-a-b)
    (hbias : β ≤ ‖𝔼 x : C, q x‖)
    (happrox : ∀ h ∈ H, ∀ x ∈ C, ‖derivative q h x-c h*F h x‖ ≤ a)
    (hstable : ∀ h ∈ H, (𝔼 x : G, |normalized C (x+h)-normalized C x|) ≤ b) :
    ∃ D : Finset (AddChar G ℂ), (D.card : ℝ) ≤ 2/η^2 ∧
      ∀ {δ γ : ℝ}, ∀ y ∈ bohr D γ,
        (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ δ →
        ∀ h ∈ H, ‖F h y-1‖ ≤ δ/ε+γ := by
  obtain ⟨D,hD,hphase⟩ := exists_weighted_spectrum_phase C hC q (fun x _ ↦ (hq x).le)
    hη hε hε1 herr
  refine ⟨D,hD,?_⟩
  intro δ γ y hy hyC h hh
  apply hphase y hy hyC
  exact hbudget.trans (biased_derivative_coefficient C hC q hq h (c h) (hc h hh)
    (F h) hbias (happrox h hh) (hstable h hh))

/-- If the approximate characters represent the normalized polarizations,
the same bounded-rank refinement makes those polarizations almost trivial. -/
theorem biased_polarization_control (C H : Finset G) (hC : C.Nonempty)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (F : G → AddChar G ℂ)
    {β a b η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (herr : ε ≤ η^2/2) (hbudget : η ≤ β-a-b)
    (hbias : β ≤ ‖𝔼 x : C, q x‖)
    (happrox : ∀ h ∈ H, ∀ x ∈ C,
      ‖derivative q h x-derivative q h 0*F h x‖ ≤ a)
    (hstable : ∀ h ∈ H, (𝔼 x : G, |normalized C (x+h)-normalized C x|) ≤ b) :
    ∃ D : Finset (AddChar G ℂ), (D.card : ℝ) ≤ 2/η^2 ∧
      ∀ {δ γ : ℝ}, ∀ y ∈ C, y ∈ bohr D γ →
        (𝔼 x : G, |normalized C (x+y)-normalized C x|) ≤ δ →
        ∀ h ∈ H, ‖localPolar q h y-1‖ ≤ a+δ/ε+γ := by
  obtain ⟨D,hD,hphase⟩ := biased_derivative_spectrum_control C H hC q hq F
    (fun h ↦ derivative q h 0) (fun h _ ↦ derivative_norm_one q hq h 0)
    hη hε hε1 herr hbudget hbias happrox hstable
  refine ⟨D,hD,?_⟩
  intro δ γ y hy hyD hyC h hh
  have he : ‖localPolar q h y-F h y‖ ≤ a := by
    have ht := happrox h hh y hy
    have hid : derivative q h y-derivative q h 0*F h y =
        derivative q h 0*(localPolar q h y-F h y) := by
      rw [derivative_eq_localPolar q hq h y]
      ring
    simpa only [hid,norm_mul,derivative_norm_one q hq,one_mul] using ht
  have ht := (norm_sub_le_norm_sub_add_norm_sub (localPolar q h y) (F h y) 1).trans
    (add_le_add he (hphase y hyD hyC h hh))
  linarith

#print axioms biased_derivative_coefficient
#print axioms biased_polarization_control
end Erdos3BiasedPhaseSpectrum
