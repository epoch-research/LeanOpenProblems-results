import Submission.MomentOrderConstants

/-!
# The totient correction does not remove a fixed logarithmic cutoff loss

These are upper bounds for the arithmetic correction in a truncated harmonic
main term. They do not bound the full shifted-prime moment from above or
provide a missing progression-distribution estimate.
-/

open Nat Filter
open scoped Classical BigOperators Topology

namespace Erdos821.HigherDivisors

noncomputable def totientHarmonicMoment (k A : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 A, (tau k n : ℝ)/(n.totient : ℝ)

lemma totientHarmonicMoment_le_cost (k A : ℕ) (hk : 1 ≤ k) :
    totientHarmonicMoment k A ≤ eulerCost k * harmonicMoment k A := by
  have hc := harmonicMoment_totient_ratio_le_cost (k-1) A
  rw [Nat.sub_add_cancel hk] at hc
  apply le_trans (Finset.sum_le_sum (fun n hn => ?_)) hc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hphi : (0 : ℝ) < n.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hn).1
  have hphi_le : (n.totient : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
  have hratio : (1 : ℝ) ≤ (n : ℝ)/(n.totient : ℝ) := (one_le_div hphi).mpr hphi_le
  have hsq : (n : ℝ)/(n.totient : ℝ) ≤ ((n : ℝ)/(n.totient : ℝ))^2 := by nlinarith
  calc
    (tau k n : ℝ)/(n.totient : ℝ) =
        (tau k n : ℝ)*((n : ℝ)/(n.totient : ℝ))/(n : ℝ) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)) hn0.le

lemma totientHarmonicMoment_rankin_normalized (k A : ℕ) (hk : 1 ≤ k) (hA : 1 < A)
    (L θ : ℝ)
    (hcutoff : Real.log A + (k : ℝ) ≤ θ*L) :
    totientHarmonicMoment k A ≤
      (eulerCost k * (Real.exp 1 / (k : ℝ))^k * θ^k) * L^k := by
  have hlog : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast hA)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log A + (k : ℝ)) hcutoff k
  calc
    _ ≤ eulerCost k * harmonicMoment k A := totientHarmonicMoment_le_cost k A hk
    _ ≤ eulerCost k * ((Real.exp 1 / (k : ℝ))^k * (Real.log A + (k : ℝ))^k) :=
      mul_le_mul_of_nonneg_left (harmonicMoment_rankin_optimized k A hk hA) (eulerCost_pos k).le
    _ ≤ eulerCost k * ((Real.exp 1 / (k : ℝ))^k * (θ*L)^k) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp (by positivity)) (eulerCost_pos k).le
    _ = _ := by rw [mul_pow]; ring

/-- Even retaining the full totient arithmetic correction, the factorial-
normalized Rankin coefficient at a fixed cutoff θ<1 tends to zero. -/
theorem tendsto_factorial_totient_cutoff_coefficient (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun k : ℕ => (k.factorial : ℝ) * eulerCost k *
      (Real.exp 1 / (k : ℝ))^k * θ^k) atTop (𝓝 0) := by
  have ht := (tendsto_polynomial_eulerCost_geometric 1 θ hθ hθ1).const_mul (Real.exp 1)
  simp only [mul_zero] at ht
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [] with k
    positivity [eulerCost_pos k]
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have h := mul_le_mul_of_nonneg_right (factorial_rankin_coefficient_le k hk)
      (mul_nonneg (eulerCost_pos k).le (pow_nonneg hθ k))
    convert h using 1 <;> ring

/-- The same conclusion with the successor factorial, matching the order
of the shifted-prime moment obtained from the divisor progression sum. -/
theorem tendsto_successor_factorial_totient_cutoff_coefficient (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun k : ℕ => ((k+1).factorial : ℝ) * eulerCost k *
      (Real.exp 1 / (k : ℝ))^k * θ^k) atTop (𝓝 0) := by
  have h := (tendsto_factorial_rough_coefficient θ hθ hθ1).add
    (tendsto_factorial_totient_cutoff_coefficient θ hθ hθ1)
  simp only [add_zero] at h
  convert h using 1
  ext k
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

end Erdos821.HigherDivisors
