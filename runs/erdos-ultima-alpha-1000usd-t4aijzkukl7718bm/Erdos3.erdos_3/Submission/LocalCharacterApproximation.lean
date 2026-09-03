import Submission.ExactPhaseLinearObstruction

/-! A local multiplicative phase is an approximate ambient character on a
translation-stability window. No exact extension of a local character is
assumed. All Fourier and window-density losses are explicit. -/
namespace Erdos3LocalCharacterApproximation
open Finset Erdos3ExactPhaseLinearObstruction Erdos3StableMaskedUniformity
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3CorrelationSifting
  Erdos3RelativeSpectrumPhase Erdos3FourierSmoothing
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def boundary (W : Finset G) (h : G) : ℝ :=
  𝔼 x : G, |indicator W (x+h)-indicator W x|

/-- Only multiplicativity on the overlap is needed. -/
lemma mask_translation_error (W : Finset G) (q : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (h : G) (c : ℂ) (hc : ‖c‖ = 1)
    (hlin : ∀ x ∈ W, x+h ∈ W → q (x+h) = c*q x) (x : G) :
    ‖mask W q (x+h)-c*mask W q x‖ ≤ |indicator W (x+h)-indicator W x| := by
  by_cases hx : x ∈ W <;> by_cases hxh : x+h ∈ W
  · simp [mask,indicator,hx,hxh,hlin x hx hxh]
  · simp [mask,indicator,hx,hxh,norm_mul,hq,hc]
  · simp [mask,indicator,hx,hxh,hq]
  · simp [mask,indicator,hx,hxh]

lemma mask_derivative_error (W : Finset G) (q : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (h : G) (c : ℂ) (hc : ‖c‖ = 1)
    (hlin : ∀ x ∈ W, x+h ∈ W → q (x+h) = c*q x) (x : G) :
    ‖derivative (mask W q) h x-c*(indicator W x : ℂ)‖ ≤
      |indicator W (x+h)-indicator W x| := by
  by_cases hx : x ∈ W <;> by_cases hxh : x+h ∈ W
  · simp only [derivative,mask,if_pos hx,if_pos hxh,hlin x hx hxh,
      mul_assoc,mul_conj_eq_one (hq x),mul_one,indicator,if_pos hx,if_pos hxh]
    simp
  · simp [derivative,mask,indicator,hx,hxh,hc]
  · simp [derivative,mask,indicator,hx,hxh]
  · simp [derivative,mask,indicator,hx,hxh]

lemma derivative_mean_error (W : Finset G) (q : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (h : G) (c : ℂ) (hc : ‖c‖ = 1)
    (hlin : ∀ x ∈ W, x+h ∈ W → q (x+h) = c*q x) :
    ‖(𝔼 x : G, derivative (mask W q) h x)-c*(density W : ℂ)‖ ≤ boundary W h := by
  have he : (𝔼 x : G, c*(indicator W x : ℂ)) = c*(density W : ℂ) := by
    rw [← mul_expect,← Complex.ofReal_expect,expect_indicator]
  rw [← he,← expect_sub_distrib]
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    (expect_le_expect (fun x _ ↦ mask_derivative_error W q hq h c hc hlin x))

/-- A nonzero Fourier coefficient of a local phase controls its deviation
from that ambient character on every admissible translation. -/
theorem local_phase_character_error (W : Finset G) (q : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (ψ : AddChar G ℂ) (h : G) (c : ℂ) (hc : ‖c‖ = 1)
    (hlin : ∀ x ∈ W, x+h ∈ W → q (x+h) = c*q x) :
    ‖hat (mask W q) ψ‖*‖ψ h-c‖ ≤ boundary W h := by
  have he : hat (fun x ↦ mask W q (x+h)-c*mask W q x) ψ =
      (ψ h-c)*hat (mask W q) ψ := by
    unfold hat
    simp only [sub_mul,mul_assoc,expect_sub_distrib,← mul_expect]
    change hat (fun x ↦ mask W q (x+h)) ψ-c*hat (mask W q) ψ =
      ψ h*hat (mask W q) ψ-c*hat (mask W q) ψ
    rw [hat_shift]
  calc
    _ = ‖hat (fun x ↦ mask W q (x+h)-c*mask W q x) ψ‖ := by
      rw [he,norm_mul,mul_comm]
    _ ≤ 𝔼 x : G, ‖mask W q (x+h)-c*mask W q x‖ := norm_hat_le _ _
    _ ≤ _ := expect_le_expect (fun x _ ↦ mask_translation_error W q hq h c hc hlin x)

/-- A stable family of locally multiplicative translations forces a large
masked U2 value. The density costs are density(P)*density(W)^2/4. -/
theorem local_phase_U2_lower (W P : Finset G) (q c : G → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h ∈ P, ‖c h‖ = 1)
    (hlin : ∀ h ∈ P, ∀ x ∈ W, x+h ∈ W → q (x+h) = c h*q x)
    (hstable : ∀ h ∈ P, boundary W h ≤ density W/2) :
    density P*(density W)^2/4 ≤ uniformityPower 1 (mask W q) := by
  have hd : 0 ≤ density W := density_nonneg W
  have hlow (h : G) (hh : h ∈ P) : density W/2 ≤
      ‖𝔼 x : G, derivative (mask W q) h x‖ := by
    have he := (derivative_mean_error W q hq h (c h) (hc h hh) (hlin h hh)).trans (hstable h hh)
    have hn := norm_sub_norm_le (c h*(density W : ℂ))
      (𝔼 x : G, derivative (mask W q) h x)
    rw [norm_mul,hc h hh,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd,
      norm_sub_rev] at hn
    linarith
  have hpoint (h : G) : indicator P h*(density W)^2/4 ≤
      ‖𝔼 x : G, derivative (mask W q) h x‖^2 := by
    by_cases hh : h ∈ P
    · simp only [indicator,if_pos hh,one_mul]
      have ht := hlow h hh
      nlinarith [sq_nonneg (‖𝔼 x : G, derivative (mask W q) h x‖-density W/2)]
    · simp only [indicator,if_neg hh,zero_mul,zero_div]
      exact sq_nonneg _
  calc
    _ = 𝔼 h : G, indicator P h*(density W)^2/4 := by
      rw [← expect_div,← expect_mul,expect_indicator]
    _ ≤ _ := expect_le_expect (fun h _ ↦ hpoint h)

/-- Finds an ambient character using only local overlap multiplicativity
and a stable positive-density family of translations. -/
theorem exists_local_phase_character (W P : Finset G) (hW : W.Nonempty)
    (q c : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h ∈ P, ‖c h‖ = 1)
    (hlin : ∀ h ∈ P, ∀ x ∈ W, x+h ∈ W → q (x+h) = c h*q x)
    (hstable : ∀ h ∈ P, boundary W h ≤ density W/2) :
    ∃ ψ : AddChar G ℂ,
      density P*density W ≤ 4*‖hat (mask W q) ψ‖^2 ∧
      ∀ h ∈ P, ‖hat (mask W q) ψ‖*‖ψ h-c h‖ ≤ boundary W h := by
  obtain ⟨ψ,hψ⟩ := exists_large_fourier_with_energy (mask W q)
  rw [mask_unit_energy W q hq] at hψ
  have hU := (local_phase_U2_lower W P q c hq hc hlin hstable).trans hψ
  have hd := density_pos W hW
  refine ⟨ψ,?_,fun h hh ↦ local_phase_character_error W q hq ψ h (c h) (hc h hh) (hlin h hh)⟩
  nlinarith

lemma boundary_normalized (W : Finset G) (hW : W.Nonempty) (h : G) :
    boundary W h = density W*(𝔼 x : G, |normalized W (x+h)-normalized W x|) := by
  have hd := density_pos W hW
  have he (x : G) : |normalized W (x+h)-normalized W x| =
      |indicator W (x+h)-indicator W x|/density W := by
    rw [normalized,normalized,← sub_div,abs_div,abs_of_pos hd]
  simp_rw [he]
  rw [← expect_div]
  exact (mul_div_cancel₀ (boundary W h) hd.ne').symm

/-- A normalized estimate. Once a character is selected using P, it works
on every other translation where overlap multiplicativity is valid. The
smaller stability window can thus be chosen independently of P. -/
theorem exists_normalized_local_character (W P : Finset G) (hW : W.Nonempty)
    (q c : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h ∈ P, ‖c h‖ = 1)
    (hlin : ∀ h ∈ P, ∀ x ∈ W, x+h ∈ W → q (x+h) = c h*q x)
    (hstable : ∀ h ∈ P, boundary W h ≤ density W/2)
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : 4*ρ^2*density W ≤ density P) :
    ∃ ψ : AddChar G ℂ,
      ρ ≤ ‖𝔼 x : W, q x*conj (ψ x)‖ ∧
      ∀ (h : G) (z : ℂ), ‖z‖ = 1 →
        (∀ x ∈ W, x+h ∈ W → q (x+h) = z*q x) →
        ∀ δ : ℝ, (𝔼 x : G, |normalized W (x+h)-normalized W x|) ≤ δ →
          ‖ψ h-z‖ ≤ δ/ρ := by
  obtain ⟨ψ,hψ,_⟩ := exists_local_phase_character W P hW q c hq hc hlin hstable
  have hd := density_pos W hW
  have hcoef : ρ*density W ≤ ‖hat (mask W q) ψ‖ := by
    have hh := mul_le_mul_of_nonneg_right hsize hd.le
    have hn := norm_nonneg (hat (mask W q) ψ)
    have hp : 0 < ρ*density W := mul_pos hρ hd
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

#print axioms exists_local_phase_character
#print axioms exists_normalized_local_character
end Erdos3LocalCharacterApproximation
