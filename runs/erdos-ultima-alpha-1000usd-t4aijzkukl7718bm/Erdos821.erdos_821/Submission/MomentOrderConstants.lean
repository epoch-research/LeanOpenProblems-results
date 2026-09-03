import Submission.WeightedRoughPrimes

/-!
# Divisor-order constants in the proposed moment comparison

A factorial-scale lower moment would beat the existing rough-prime main
coefficient at sufficiently large order. These are estimates of the
coefficients only: the missing lower moment on shifted primes is not
assumed as a theorem here.
-/

open Nat Filter
open scoped Classical Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

/-- A convenient upper half of Stirling, retaining only a polynomial
factor after cancellation of the Rankin coefficient. -/
lemma factorial_rankin_coefficient_le (k : ℕ) (hk : 1 ≤ k) :
    (k.factorial : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k ≤ Real.exp 1 * k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hst : Stirling.stirlingSeq k ≤ Real.exp 1 / Real.sqrt 2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simpa only [Function.comp_apply, Nat.succ_eq_add_one, Nat.zero_add,
      Stirling.stirlingSeq_one] using Stirling.stirlingSeq'_antitone (Nat.zero_le j)
  have hsqrt : Real.sqrt (k : ℝ) ≤ k := by
    have hs := Real.sq_sqrt hk0.le
    have hz := Real.sqrt_nonneg (k : ℝ)
    nlinarith
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hid : (k.factorial : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k =
      Stirling.stirlingSeq k * Real.sqrt (2 * (k : ℝ)) := by
    unfold Stirling.stirlingSeq
    rw [div_pow, div_pow]
    field_simp
  calc
    _ = _ := hid
    _ ≤ (Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hst (Real.sqrt_nonneg _)
    _ = Real.exp 1 * Real.sqrt (k : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos _).le

/-- The Euler-product cost remains negligible against any fixed geometric
saving, even after multiplying by a fixed power of the divisor order. -/
theorem tendsto_polynomial_eulerCost_geometric (d : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun k : ℕ => (k : ℝ)^d * eulerCost k * ρ^k) atTop (𝓝 0) := by
  rcases hρ.eq_or_lt with hρ | hρ
  · subst ρ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp [show k ≠ 0 by omega]
  let b := (ρ + 1) / 2
  have hρb : ρ < b := by dsimp [b]; linarith
  have hb : 0 < b := hρ.trans hρb
  have hb1 : b < 1 := by dsimp [b]; linarith
  let η := Real.log (b / ρ)
  have hη : 0 < η := Real.log_pos ((one_lt_div hρ).mpr hρb)
  have hexp : Real.exp η * ρ = b := by
    dsimp [η]
    rw [Real.exp_log (div_pos hb hρ), div_mul_cancel₀ _ hρ.ne']
  have hnonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ (k : ℝ)^d * eulerCost k * ρ^k := by
    filter_upwards [] with k
    exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (eulerCost_pos k).le)
      (pow_nonneg hρ.le _)
  apply squeeze_zero' hnonneg ?_ (tendsto_pow_const_mul_const_pow_of_lt_one d hb.le hb1)
  filter_upwards [eventually_eulerCost_le_exp η hη] with k hk
  calc
    (k : ℝ)^d * eulerCost k * ρ^k ≤ (k : ℝ)^d * Real.exp (η * (k : ℝ)) * ρ^k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (pow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hρ.le _)
    _ = (k : ℝ)^d * b^k := by
      rw [mul_comm η (k : ℝ), Real.exp_nat_mul, mul_assoc, ← mul_pow, hexp]

/-- Relative to a factorial-scale main term, the rough-prime Rankin
coefficient tends to zero as the order grows. This is the coefficient
comparison that would make a sharp all-order lower moment useful. -/
theorem tendsto_factorial_rough_coefficient (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun k : ℕ => (k : ℝ) * (k.factorial : ℝ) *
      (Real.exp 1 / (k : ℝ))^k * eulerCost k * ρ^k) atTop (𝓝 0) := by
  have hnonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ (k : ℝ) * (k.factorial : ℝ) *
      (Real.exp 1 / (k : ℝ))^k * eulerCost k * ρ^k := by
    filter_upwards [] with k
    positivity [eulerCost_pos k]
  have ht := (tendsto_polynomial_eulerCost_geometric 2 ρ hρ hρ1).const_mul (Real.exp 1)
  simp only [mul_zero] at ht
  apply squeeze_zero' hnonneg ?_ ht
  filter_upwards [eventually_ge_atTop 1] with k hk
  have h := mul_le_mul_of_nonneg_left (factorial_rankin_coefficient_le k hk)
    (Nat.cast_nonneg k)
  have h' := mul_le_mul_of_nonneg_right h
    (mul_nonneg (eulerCost_pos k).le (pow_nonneg hρ k))
  nlinarith only [h']

/-- For each fixed smoothing ratio and fixed sieve constant, some order
makes the rough coefficient strictly smaller than `1/k!`. The arithmetic
lower bound for the TOTAL shifted-prime moment is a separate obligation. -/
theorem exists_order_rough_coefficient_lt_factorial (ρ C : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (B : ℕ) :
    ∃ k : ℕ, B < k ∧ 2 ≤ k ∧
      C * (k : ℝ) * (Real.exp 1 / (k : ℝ))^k * eulerCost k * ρ^k <
        1 / (k.factorial : ℝ) := by
  have ht := (tendsto_factorial_rough_coefficient ρ hρ hρ1).const_mul C
  simp only [mul_zero] at ht
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let k := max (B + 2) M
  have hkB : B < k := lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hk2 : 2 ≤ k := (show 2 ≤ B + 2 by omega).trans (le_max_left _ _)
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  refine ⟨k, hkB, hk2, (lt_div_iff₀ hf).mpr ?_⟩
  convert hM k (le_max_right _ _) using 1
  ring

/-- A fixed multiplicative loss in the logarithmic cutoff cannot be
repaired by choosing one of the `k+1` distinguished factors. -/
theorem tendsto_symmetrized_cutoff_ratio (θ ρ : ℝ) (hθ : 0 ≤ θ) (hρ : 0 < ρ)
    (hθρ : θ < ρ) :
    Tendsto (fun k : ℕ => (k + 1 : ℝ) * (θ / ρ)^k) atTop (𝓝 0) := by
  have hq : 0 ≤ θ / ρ := div_nonneg hθ hρ.le
  have hq1 : θ / ρ < 1 := (div_lt_one hρ).mpr hθρ
  have h1 := tendsto_self_mul_const_pow_of_lt_one hq hq1
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  convert h1.add h2 using 1
  · ext k
    ring
  · norm_num

/-- A finite normalization of the actual rough-sieve main expression.
Here `L` is the logarithmic output scale; the two hypotheses on cutoffs
remain explicit. -/
theorem rough_sieve_main_le_normalized (k X K J : ℕ) (hk : 2 ≤ k) (hK : 1 < K)
    (L ρ κ : ℝ) (hL : 0 < L) (hκ : 0 < κ)
    (hcofactor : Real.log K + k ≤ ρ * L) (hsieve : κ * L ≤ (J : ℝ) * Real.log 2) :
    (k : ℝ) * (16 * (X : ℝ) / ((J : ℝ) * Real.log 2)^2) *
      (eulerCost k * harmonicMoment k K) ≤
    (16 / κ^2 * (k : ℝ) * (Real.exp 1 / (k : ℝ))^k * eulerCost k * ρ^k) *
      (X : ℝ) * L^(k-2) := by
  have hKL : 0 ≤ Real.log K + (k : ℝ) := by
    have hlog : 0 < Real.log K := Real.log_pos (by exact_mod_cast hK)
    positivity
  have hH : harmonicMoment k K ≤
      (Real.exp 1 / (k : ℝ))^k * ρ^k * L^k := by
    apply (harmonicMoment_rankin_optimized k K (by omega) hK).trans
    have hp := pow_le_pow_left₀ hKL hcofactor k
    rw [mul_pow] at hp
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
      (pow_nonneg (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) _)
  have hden : (κ * L)^2 ≤ ((J : ℝ) * Real.log 2)^2 :=
    pow_le_pow_left₀ (mul_pos hκ hL).le hsieve 2
  have hcoef : 16 * (X : ℝ) / ((J : ℝ) * Real.log 2)^2 ≤
      16 * (X : ℝ) / (κ * L)^2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hbig := mul_le_mul
    (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg k))
    (mul_le_mul_of_nonneg_left hH (eulerCost_pos k).le)
    (mul_nonneg (eulerCost_pos k).le (harmonicMoment_nonneg k K))
    (by positivity : 0 ≤ (k : ℝ) * (16 * (X : ℝ) / (κ * L)^2))
  apply hbig.trans_eq
  have hpow : L^k = L^(k-2) * L^2 := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hpow]
  field_simp

/-- The favorable coefficient comparison can be applied uniformly at all
scales satisfying the explicit cutoff conditions. The total shifted-prime
moment lower bound is still absent. -/
theorem exists_order_rough_main_lt_factorial (ρ κ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hκ : 0 < κ) (B : ℕ) :
    ∃ k : ℕ, B < k ∧ 2 ≤ k ∧ ∀ X K J : ℕ, 0 < X → 1 < K →
      ∀ L : ℝ, 0 < L → Real.log K + k ≤ ρ * L →
      κ * L ≤ (J : ℝ) * Real.log 2 →
      (k : ℝ) * (16 * (X : ℝ) / ((J : ℝ) * Real.log 2)^2) *
        (eulerCost k * harmonicMoment k K) <
        (X : ℝ) * L^(k-2) / (k.factorial : ℝ) := by
  obtain ⟨k, hkB, hk2, hk⟩ := exists_order_rough_coefficient_lt_factorial ρ (16 / κ^2) hρ hρ1 B
  refine ⟨k, hkB, hk2, ?_⟩
  intro X K J hX hK L hL hcofactor hsieve
  apply (rough_sieve_main_le_normalized k X K J hk2 hK L ρ κ hL hκ hcofactor hsieve).trans_lt
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have h := mul_lt_mul_of_pos_right hk (mul_pos hXR (pow_pos hL (k-2)))
  convert h using 1 <;> ring

end Erdos821.HigherDivisors
