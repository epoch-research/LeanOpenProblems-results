import Submission.OptimizedSupport

/-!
# Necessary size of the existing Rankin budget

These lemmas audit an auxiliary upper-bound method; they do not prove or
negate the conjecture. In particular, the quadratic threshold already follows
from the factor `A^2`, independently of the bound on the exponential constant.
-/

open Nat Filter

namespace Erdos821

lemma quadratic_log_necessary_for_rankin_budget (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n) (C : ℝ) (hC : 0 ≤ C)
    (hbudget : ((2 : ℝ) ^ k) ^ 2 * Real.exp C ≤ (n : ℝ) ^ (1 / (k : ℝ))) :
    2 * Real.log 2 * (k : ℝ) ^ 2 ≤ Real.log n := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : ((2 : ℝ) ^ k) ^ 2 ≤ (n : ℝ) ^ (1 / (k : ℝ)) := by
    calc
      _ ≤ ((2 : ℝ) ^ k) ^ 2 * Real.exp C :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr hC)
      _ ≤ _ := hbudget
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ k) ^ 2) hpow
  rw [Real.log_pow, Real.log_pow, Real.log_rpow hnR] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog hkR.le
  field_simp at hmul
  norm_num at hmul
  nlinarith only [hmul]

lemma smooth_rankin_budget_forces_quadratic_log (k n : ℕ)
    (hk : 2 ≤ k) (hn : 0 < n)
    (hbudget : ((2 : ℝ) ^ k) ^ 2 *
        Real.exp (smoothRankinConstant (1 - 1 / (k : ℝ))
          (1 + 1 / (k : ℝ)) * 16) ≤ (n : ℝ) ^ (1 / (k : ℝ))) :
    2 * Real.log 2 * (k : ℝ) ^ 2 ≤ Real.log n := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hinv : 1 / (k : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hkR
  exact quadratic_log_necessary_for_rankin_budget k n (by omega) hn _
    (mul_nonneg (smoothRankinConstant_nonneg (by linarith)) (by norm_num)) hbudget

/-- The existing optimized upper envelope is eventually strictly larger than
every fixed-power target in the conjecture. This is a statement about the
explicit envelope, not a lower bound for `g`. -/
lemma eventually_optimized_envelope_gt_fixed_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 - ε) < (n : ℝ) ^
        (1 - ((Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 1 : ℕ) : ℝ) /
          (2 : ℝ) ^ (Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 4)) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tendsto_optimized_support_rankin_exponent_loss.eventually (gt_mem_nhds hε)]
    with n hn hloss
  apply Real.rpow_lt_rpow_of_exponent_lt
    (by exact_mod_cast (show 1 < n by omega))
  linarith

#print axioms quadratic_log_necessary_for_rankin_budget
#print axioms smooth_rankin_budget_forces_quadratic_log
#print axioms eventually_optimized_envelope_gt_fixed_power

end Erdos821
