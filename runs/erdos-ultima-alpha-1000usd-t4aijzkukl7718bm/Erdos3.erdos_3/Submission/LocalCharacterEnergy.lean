import Submission.LocalCharacterApproximation
import Submission.LocalFactorMean

/-! Exact additive-energy preservation by a local character. The Fourier
coefficient lower bound is independent of a translation-stability tolerance. -/
namespace Erdos3LocalCharacterEnergy
open Finset Erdos3LocalCharacterApproximation Erdos3LocalFactorMean
  Erdos3ExactPhaseLinearObstruction Erdos3StableMaskedUniformity
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3CorrelationSifting
  Erdos3FourierSmoothing
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Local multiplicativity on every overlap preserves the masked U2 power
exactly. No multiplicativity is required when the overlap is empty. -/
theorem local_character_U2_eq (W : Finset G) (q c : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h, ‖c h‖ = 1)
    (hlin : ∀ h x, x ∈ W → x+h ∈ W → q (x+h) = c h*q x) :
    uniformityPower 1 (mask W q) = uniformityPower 1 (mask W (fun _ ↦ 1)) := by
  have he (h x : G) : derivative (mask W q) h x =
      c h*derivative (mask W (fun _ ↦ 1)) h x := by
    by_cases hx : x ∈ W <;> by_cases hxh : x+h ∈ W
    · simp only [derivative,mask,if_pos hx,if_pos hxh,hlin h x hx hxh,
        mul_assoc,mul_conj_eq_one (hq x),map_one,mul_one]
    · simp [derivative,mask,hx,hxh]
    · simp [derivative,mask,hx,hxh]
    · simp [derivative,mask,hx,hxh]
  change (𝔼 h : G, ‖𝔼 x : G, derivative (mask W q) h x‖^2) = _
  simp only [he,← mul_expect,norm_mul,hc,one_mul]
  rfl

/-- A unit local character on W has masked U2 at least density(W)^4. -/
theorem local_character_U2_lower (W : Finset G) (q c : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h, ‖c h‖ = 1)
    (hlin : ∀ h x, x ∈ W → x+h ∈ W → q (x+h) = c h*q x) :
    (density W)^4 ≤ uniformityPower 1 (mask W q) := by
  rw [local_character_U2_eq W q c hq hc hlin]
  have he : (𝔼 x : G, mask W (fun _ ↦ 1) x) = (density W : ℂ) := by
    rw [← expect_indicator,Complex.ofReal_expect]
    apply expect_congr rfl
    intro x _
    by_cases hx : x ∈ W <;> simp [mask,indicator,hx]
  have ht := mean_power_le_uniformity 1 (mask W (fun _ ↦ 1))
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (density_nonneg W)] at ht
  exact ht

/-- Normalized character approximation with a correlation parameter depending
only on density(W), not on the size of a fine translation window. -/
theorem exists_energy_local_character (W : Finset G) (hW : W.Nonempty)
    (q c : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h, ‖c h‖ = 1)
    (hlin : ∀ h x, x ∈ W → x+h ∈ W → q (x+h) = c h*q x)
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : ρ^2 ≤ density W) :
    ∃ ψ : AddChar G ℂ,
      ρ ≤ ‖𝔼 x : W, q x*conj (ψ x)‖ ∧
      ∀ (h : G) (z : ℂ), ‖z‖ = 1 →
        (∀ x ∈ W, x+h ∈ W → q (x+h) = z*q x) →
        ∀ δ : ℝ, (𝔼 x : G, |normalized W (x+h)-normalized W x|) ≤ δ →
          ‖ψ h-z‖ ≤ δ/ρ := by
  obtain ⟨ψ,hψ⟩ := exists_large_fourier_with_energy (mask W q)
  rw [mask_unit_energy W q hq] at hψ
  have hU := (local_character_U2_lower W q c hq hc hlin).trans hψ
  have hd := density_pos W hW
  have hcoef : ρ*density W ≤ ‖hat (mask W q) ψ‖ := by
    have hh : ρ^2*(density W)^3 ≤ (density W)^4 := by
      nlinarith [mul_le_mul_of_nonneg_right hsize (pow_nonneg hd.le 3)]
    have hn := norm_nonneg (hat (mask W q) ψ)
    have hp : 0 < ρ*density W := mul_pos hρ hd
    have hs : (ρ*density W)^2 ≤ ‖hat (mask W q) ψ‖^2 := by nlinarith
    nlinarith [sq_nonneg (‖hat (mask W q) ψ‖-ρ*density W)]
  refine ⟨ψ,?_,?_⟩
  · rw [mask_hat_normalized W hW q ψ,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hd] at hcoef
    nlinarith
  · intro h z hz hlinz δ hδ
    have he := local_phase_character_error W q hq ψ h z hz hlinz
    rw [boundary_normalized W hW h] at he
    have hh := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (ψ h-z))
    have hb := mul_le_mul_of_nonneg_left hδ hd.le
    apply (le_div_iff₀ hρ).mpr
    nlinarith

#print axioms local_character_U2_eq
#print axioms exists_energy_local_character
end Erdos3LocalCharacterEnergy
