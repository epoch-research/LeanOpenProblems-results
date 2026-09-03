import Submission.RobustLocalCharacter

/-! Radius-independent local character approximation on Bohr windows.
Small polarization can be linearized at a prescribed center; no bias or
phase-based choice of that center is needed. -/
namespace Erdos3RobustBohrLinearization
open Finset Erdos3RobustLocalCharacter Erdos3DoublingOverlapEnergy
  Erdos3FiniteBohr Erdos3BohrCovering Erdos3RelativeStableBohr Erdos3BohrTranslation
  Erdos3LocalQuadraticPolarization Erdos3LocalQuadraticProgressions
  Erdos3FiniteUniformity Erdos3RootFreeQuadraticDilation Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The normalized Fourier correlation 1/(2*9^d) is independent of r and z.
This permits choosing a fine stability tolerance without a circular loss. -/
theorem robust_bohr_character (D : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hst : RelativeStable D z r)
    (q c : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hc : ∀ h, ‖c h‖ = 1)
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (herr : ∀ h x, x ∈ bohr D r → x+h ∈ bohr D r → ‖q (x+h)-c h*q x‖ ≤ a) :
    ∃ ψ : AddChar G ℂ, ∀ h ∈ bohr D (relativeWidth D z r),
      ‖ψ h-c h‖ ≤ 2*(9 : ℝ)^D.card*(1/(z : ℝ)+a) := by
  have hρ : 0 < 1/(2*(9 : ℝ)^D.card) := by positivity
  have hcost : (1/(2*(9 : ℝ)^D.card))^2*(81 : ℝ)^D.card ≤ (1-a)^2 := by
    have he : (1/(2*(9 : ℝ)^D.card))^2*(81 : ℝ)^D.card = 1/4 := by
      rw [show (81 : ℝ) = 9^2 by norm_num, ← pow_mul, Nat.mul_comm 2 D.card, pow_mul]
      field_simp
      ring
    rw [he]
    nlinarith
  obtain ⟨ψ,_,hψ⟩ := exists_robust_local_character (bohr D r) ⟨0,bohr_zero D hr.le⟩
    (by positivity : 0 < (81 : ℝ)^D.card) (bohr_difference_doubling D hr)
    q c hq hc ha (by linarith) hρ hcost herr
  refine ⟨ψ,?_⟩
  intro h hh
  have ht := normalized_bohr_translation_le D hr.le (relativeWidth_pos D hz hr).le
    (by positivity) hst hh
  have he := hψ h (1/(z : ℝ)) ht
  simpa only [one_div, div_inv_eq_mul, mul_comm] using he

lemma translated_polar_error (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (b h x : G) :
    ‖q (b+(x+h))-derivative q h b*q (b+x)‖ =
      ‖localPolar (fun y ↦ q (b+y)) h x-1‖ := by
  let f : G → ℂ := fun y ↦ q (b+y)
  have hf (y : G) : ‖f y‖ = 1 := hq _
  have hc : derivative f h 0 = derivative q h b := by simp only [f,derivative,zero_add,add_zero]
  have he : f (x+h)-derivative f h 0*f x =
      derivative f h 0*(localPolar f h x-1)*f x := by
    have ht := unit_conj_cancel (hf x) (show f (x+h)*conj (f x) = derivative f h x from rfl)
    rw [ht,derivative_eq_localPolar f hf h x]
    ring
  change ‖f (x+h)-derivative q h b*f x‖ = ‖localPolar f h x-1‖
  rw [← hc,he,norm_mul,norm_mul,derivative_norm_one f hf,hf,one_mul,mul_one]

/-- A linearizing character exists at any prescribed center with small
polarization on overlaps. The center need not be chosen for phase bias. -/
theorem prescribed_center_linearization (D : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hst : RelativeStable D z r)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (b : G)
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (hpolar : ∀ h x, x ∈ bohr D r → x+h ∈ bohr D r →
      ‖localPolar (fun y ↦ q (b+y)) h x-1‖ ≤ a) :
    ∃ ψ : AddChar G ℂ, ∀ h ∈ bohr D (relativeWidth D z r),
      ‖q (b+h)-q b*ψ h‖ ≤ 2*(9 : ℝ)^D.card*(1/(z : ℝ)+a) := by
  obtain ⟨ψ,hψ⟩ := robust_bohr_character D hr hz hst (fun x ↦ q (b+x))
    (fun h ↦ derivative q h b) (fun x ↦ hq _) (fun h ↦ derivative_norm_one q hq h b) ha ha2
    (fun h x hx hxh ↦ by rw [translated_polar_error q hq]; exact hpolar h x hx hxh)
  refine ⟨ψ,?_⟩
  intro h hh
  rw [← first_derivative_error q hq ψ b h,norm_sub_rev]
  exact hψ h hh

#print axioms robust_bohr_character
#print axioms prescribed_center_linearization
end Erdos3RobustBohrLinearization
