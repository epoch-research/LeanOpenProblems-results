import Submission.LocalQuadraticU2Linearization
import Submission.QuadraticProgressionCurvature

/-! Root-free dilation of quadratic phases. Passing to a 2n-dilate converts
an nth-power phase relation into an ordinary coordinate relation, without
choosing any roots or branch labels. -/
namespace Erdos3RootFreeQuadraticDilation
open Finset Erdos3LocalQuadraticProgressions Erdos3QuadraticProgressionCurvature
  Erdos3LocalQuadraticInverse Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3BoundedFrequencyPhaseApproximation Erdos3FiniteCircleGrid Erdos3FiniteBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G]

noncomputable def rootFreeTransform (n : ℕ) (q : G → ℂ) (b x : G) : ℂ :=
  (derivative q x b)^2*(derivative (derivative q x) x b)^(2*n-1)

lemma rootFreeTransform_norm (n : ℕ) (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (b x : G) :
    ‖rootFreeTransform n q b x‖ = 1 := by
  simp only [rootFreeTransform,norm_mul,norm_pow,derivative_norm_one q hq,
    derivative_norm_one (derivative q x) (derivative_norm_one q hq x),one_pow,one_mul]

lemma doubled_choose_two (n : ℕ) : (2*n).choose 2 = n*(2*n-1) := by
  have ht := two_choose_two_add (2*n)
  by_cases hn : n = 0
  · simp [hn]
  · have hh : 2*n-1+1 = 2*n := by omega
    nlinarith

/-- This identity is valid for every unit local quadratic phase along a
progression in its domain. No divisibility or torsion assumption is needed. -/
theorem rootFreeTransform_dilation {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (n : ℕ) (b x : G) (hR : ∀ j ≤ 2*n, b+j • x ∈ R) :
    q (b+(2*n) • x) = q b*(rootFreeTransform n q b x)^n := by
  rw [local_quadratic_progression_formula hq hquad b x hR (2*n) le_rfl,doubled_choose_two]
  unfold rootFreeTransform
  rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm (2*n-1) n]
  ring

lemma first_derivative_error (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (ψ : AddChar G ℂ) (b x : G) :
    ‖derivative q x b-ψ x‖ = ‖q (b+x)-q b*ψ x‖ := by
  have he : derivative q x b-ψ x = (q (b+x)-q b*ψ x)*conj (q b) := by
    unfold derivative
    rw [sub_mul]
    have ht : q b*ψ x*conj (q b) = ψ x := by
      calc
        _ = ψ x*(q b*conj (q b)) := by ring
        _ = _ := by rw [mul_conj_eq_one (hq b),mul_one]
    rw [ht]
  rw [he,norm_mul,Complex.norm_conj,hq,mul_one]

lemma second_derivative_three_values (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (b x : G) :
    derivative (derivative q x) x b =
      (q (b+(2 : ℕ) • x)*conj (q b))*conj (derivative q x b)^2 := by
  simp only [derivative,two_nsmul,map_mul,starRingEnd_self_apply,add_assoc]
  calc
    _ = (q (b+(x+x))*conj (q (b+x))^2*q b)*(q b*conj (q b)) := by
      rw [mul_conj_eq_one (hq b),mul_one]
      ring
    _ = _ := by ring

variable [Fintype G]

/-- Two approximate linear values suffice to control the transformed phase.
The error grows only linearly in n. -/
theorem rootFreeTransform_linear_error (n : ℕ) (hn : 0 < n)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (ψ : AddChar G ℂ) (b x : G)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h1 : ‖q (b+x)-q b*ψ x‖ ≤ δ)
    (h2 : ‖q (b+(2 : ℕ) • x)-q b*ψ ((2 : ℕ) • x)‖ ≤ δ) :
    ‖rootFreeTransform n q b x-(ψ x)^2‖ ≤ 6*(n : ℝ)*δ := by
  let u := derivative q x b
  let v := derivative (derivative q x) x b
  have hu : ‖u‖ = 1 := derivative_norm_one q hq x b
  have hv : ‖v‖ = 1 := derivative_norm_one (derivative q x) (derivative_norm_one q hq x) x b
  have huE : ‖u-ψ x‖ ≤ δ := by rw [first_derivative_error q hq]; exact h1
  have h2E : ‖q (b+(2 : ℕ) • x)*conj (q b)-(ψ x)^2‖ ≤ δ := by
    have ht := h2
    rw [← first_derivative_error q hq ψ b ((2 : ℕ) • x)] at ht
    simpa only [derivative,two_nsmul,ψ.map_add_eq_mul,← sq] using ht
  have hvE : ‖v-1‖ ≤ 3*δ := by
    have hh := unit_mul_distance
      (by rw [norm_mul,Complex.norm_conj,hq,hq,one_mul] : ‖q (b+(2 : ℕ) • x)*conj (q b)‖ = 1)
      (by rw [norm_pow,Complex.norm_conj,ψ.norm_apply,one_pow] : ‖conj (ψ x)^2‖ = 1)
      (b := conj u^2) (c := (ψ x)^2)
    have he : (ψ x)^2*conj (ψ x)^2 = 1 := by rw [← mul_pow,mul_conj_eq_one (ψ.norm_apply x),one_pow]
    rw [he,← second_derivative_three_values q hq] at hh
    have hc : ‖conj u^2-conj (ψ x)^2‖ ≤ 2*δ := by
      have hp := unit_power_distance hu (ψ.norm_apply x) 2
      norm_num only [Nat.cast_ofNat] at hp
      have he : ‖conj u^2-conj (ψ x)^2‖ = ‖u^2-(ψ x)^2‖ := by
        rw [← map_pow,← map_pow,← map_sub,Complex.norm_conj]
      rw [he]
      nlinarith
    change ‖v-1‖ ≤ _ at hh
    linarith
  have hu2 := (unit_power_distance hu (ψ.norm_apply x) 2).trans
    (mul_le_mul_of_nonneg_left huE (by norm_num : (0 : ℝ) ≤ 2))
  norm_num only [Nat.cast_ofNat] at hu2
  have hvpow := (unit_power_oscillation v hv (2*n-1)).trans
    (mul_le_mul_of_nonneg_left hvE (Nat.cast_nonneg _))
  have ht := unit_mul_distance (by rw [norm_pow,hu,one_pow] : ‖u^2‖ = 1)
    (by norm_num : ‖(1 : ℂ)‖ = 1) (b := v^(2*n-1)) (c := (ψ x)^2)
  rw [mul_one] at ht
  change ‖u^2*v^(2*n-1)-(ψ x)^2‖ ≤ _
  have he : ((2*n-1 : ℕ) : ℝ) = 2*(n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  rw [he] at hvpow
  nlinarith

#print axioms rootFreeTransform_dilation
#print axioms rootFreeTransform_linear_error
end Erdos3RootFreeQuadraticDilation
