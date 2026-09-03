import Submission.MomentOrderConstants

/-!
# Normalized local factors for shifted-prime divisor moments

The valuation weights and their generating series are evaluated exactly.
The resulting finite Euler products are subexponential in the divisor
order, uniformly in the prime set. These local identities do not assert
an asymptotic or a lower bound for the actual shifted-prime moments.
-/

open Nat Finset Filter
open scoped Classical BigOperators Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 3000000

noncomputable def primeLocalValuationWeight (p e : ℕ) : ℝ :=
  if e=0 then ((p : ℝ)-2)/((p : ℝ)-1) else (1/(p : ℝ))^e

noncomputable def primeDivisorLocalFactor (k p : ℕ) : ℝ :=
  1+(1-(1-1/(p : ℝ))^k)/((p : ℝ)-1)

lemma hasSum_primeLocal_divisor (k p : ℕ) (hp : p.Prime) :
    HasSum (fun e : ℕ => (tau (k+1) (p^e) : ℝ)*primeLocalValuationWeight p e)
      (1/(1-1/(p : ℝ))^(k+1)-1/((p : ℝ)-1)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnorm : ‖1/(p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_lt_one (by positivity)).mpr hpR
  have H := (hasSum_choose_mul_geometric_of_norm_lt_one k hnorm).sub
    (hasSum_ite_eq (0 : ℕ) (1/((p : ℝ)-1)))
  convert H using 1
  funext e
  rw [tau_prime_pow k e p hp]
  unfold primeLocalValuationWeight
  by_cases he : e=0
  · subst e
    simp only [ite_true, zero_add, Nat.choose_self, Nat.cast_one, pow_zero, one_mul]
    field_simp [show (p : ℝ)-1 ≠ 0 by linarith]
    ring
  · simp only [if_neg he, sub_zero]

lemma normalized_primeLocal_divisor_sum (k p : ℕ) (hp : p.Prime) :
    (1-1/(p : ℝ))^k *
      (∑' e : ℕ, (tau (k+1) (p^e) : ℝ)*primeLocalValuationWeight p e) =
        primeDivisorLocalFactor k p := by
  rw [(hasSum_primeLocal_divisor k p hp).tsum_eq]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpm : (p : ℝ)-1 ≠ 0 := by linarith
  have hu : 1-1/(p : ℝ) ≠ 0 := by
    have h : 1/(p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hpR
    linarith
  unfold primeDivisorLocalFactor
  rw [pow_succ]
  field_simp
  ring

lemma primeDivisorLocalFactor_ge_one (k p : ℕ) (hp : p.Prime) :
    1 ≤ primeDivisorLocalFactor k p := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hi : 1/(p : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hpR
  have hu : 0 ≤ 1-1/(p : ℝ) := by linarith
  have hu1 : 1-1/(p : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  have hpow : (1-1/(p : ℝ))^k ≤ 1 := pow_le_one₀ hu hu1
  unfold primeDivisorLocalFactor
  exact le_add_of_nonneg_right (div_nonneg (by linarith) (by linarith))

lemma primeDivisorLocalFactor_le_quadratic (k p : ℕ) (hp : p.Prime) :
    primeDivisorLocalFactor k p ≤ 1+8*(k : ℝ)*((p : ℝ)^2)⁻¹ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm : (0 : ℝ) < (p : ℝ)-1 := by linarith
  have hi : 1/(p : ℝ) ≤ 1 := (div_le_one hp0).mpr (by linarith)
  have hbern := one_add_mul_le_pow (a := -(1/(p : ℝ))) (by linarith : -2 ≤ -(1/(p : ℝ))) k
  have hnum : 1-(1-1/(p : ℝ))^k ≤ (k : ℝ)/(p : ℝ) := by
    simp only [← sub_eq_add_neg, mul_neg, mul_one_div] at hbern
    linarith
  unfold primeDivisorLocalFactor
  apply _root_.add_le_add le_rfl
  calc
    _ ≤ ((k : ℝ)/(p : ℝ))/((p : ℝ)-1) :=
      div_le_div_of_nonneg_right hnum hpm.le
    _ ≤ 8*(k : ℝ)*((p : ℝ)^2)⁻¹ := by
      rw [div_div, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ (mul_pos hp0 hpm) (sq_pos_of_pos hp0)).mpr
      have hbase : (p : ℝ)^2 ≤ 8*(p : ℝ)*((p : ℝ)-1) := by nlinarith
      have h := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg (α := ℝ) k)
      nlinarith only [h]

lemma finite_primeDivisorLocalFactor_product_le (k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, primeDivisorLocalFactor k p) ≤ eulerCost k := by
  apply le_trans _ (finite_euler_product_le k P)
  exact Finset.prod_le_prod
    (fun p hp => (by norm_num : (0 : ℝ) ≤ 1).trans (primeDivisorLocalFactor_ge_one k p (hP p hp)))
    (fun p hp => primeDivisorLocalFactor_le_quadratic k p (hP p hp))

/-- Uniform even when the finite prime set grows with the order. -/
theorem tendsto_primeDivisorLocalFactor_product_geometric (d : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → p.Prime) :
    Tendsto (fun k : ℕ => (k : ℝ)^d *
      (∏ p ∈ P k, primeDivisorLocalFactor k p)*ρ^k) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_polynomial_eulerCost_geometric d ρ hρ hρ1)
  · filter_upwards [] with k
    apply mul_nonneg
    · apply mul_nonneg (by positivity)
      exact Finset.prod_nonneg (fun p hp =>
        (by norm_num : (0 : ℝ) ≤ 1).trans (primeDivisorLocalFactor_ge_one k p (hP k p hp)))
    · exact pow_nonneg hρ k
  · filter_upwards [] with k
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (finite_primeDivisorLocalFactor_product_le k (P k) (hP k))
        (by positivity)) (pow_nonneg hρ k)

/-- The algebraic half-level coefficient remains smaller than every fixed
geometric coefficient of base greater than one half. This comparison is
NOT an upper bound for the actual shifted-prime moment. -/
theorem eventually_half_level_local_coefficient_lt (θ : ℝ) (hθ : 1/2 < θ)
    (P : ℕ → Finset ℕ) (hP : ∀ k p, p ∈ P k → p.Prime) :
    ∀ᶠ k : ℕ in atTop, ((k : ℝ)+1) *
      (∏ p ∈ P k, primeDivisorLocalFactor k p)*(1/2 : ℝ)^k < θ^k := by
  let ρ : ℝ := (1/2)/θ
  have hθ0 : 0 < θ := by linarith
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := (div_lt_one hθ0).mpr hθ
  have H := (tendsto_primeDivisorLocalFactor_product_geometric 1 ρ hρ hρ1 P hP).add
    (tendsto_primeDivisorLocalFactor_product_geometric 0 ρ hρ hρ1 P hP)
  simp only [pow_one, pow_zero, one_mul, zero_add] at H
  filter_upwards [H.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with k hk
  have hk' : ((k : ℝ)+1)*(∏ p ∈ P k, primeDivisorLocalFactor k p)*ρ^k < 1 := by
    nlinarith only [hk]
  have hh := mul_lt_mul_of_pos_right hk' (pow_pos hθ0 k)
  have he : ρ^k*θ^k = (1/2 : ℝ)^k := by
    rw [← mul_pow]
    congr 1
    dsimp [ρ]
    exact div_mul_cancel₀ _ hθ0.ne'
  simpa only [mul_assoc, he, one_mul] using hh

end Erdos821.HigherDivisors
