import Submission.PrimePowerError

/-! Finite exponential-divisor approximations to the von Mangoldt function.
Pointwise and finite-window convergence do not justify exchanging the
smoothing limit with a mean-value limit at infinity. -/
namespace Erdos972SmoothMangoldt

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Topology
open Erdos972PrimePowerError

noncomputable def expDivisorSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ) * Real.exp (-t * Real.log d)

/-- Subtracting the value at zero removes the exceptional n=1 term. -/
noncomputable def smoothMangoldt (t : ℝ) (n : ℕ) : ℝ :=
  (expDivisorSum t n - expDivisorSum 0 n) / t

lemma expDivisorSum_at_zero (n : ℕ) :
    expDivisorSum 0 n = (1 : ArithmeticFunction ℝ) n := by
  simp only [expDivisorSum, neg_zero, zero_mul, Real.exp_zero, mul_one]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [coe_mul_zeta_apply, intCoe_apply] using h

lemma hasDerivAt_expDivisorSum (n : ℕ) :
    HasDerivAt (fun t => expDivisorSum t n) (Λ n) 0 := by
  have hd (d : ℕ) : HasDerivAt (fun t : ℝ => (μ d : ℝ) * Real.exp (-t * Real.log d))
      (-(μ d : ℝ) * Real.log d) 0 := by
    have h := (((hasDerivAt_id (0:ℝ)).neg.mul_const (Real.log d)).exp).const_mul (μ d : ℝ)
    convert h using 1; simp
  have hh := HasDerivAt.fun_sum (fun d (_ : d ∈ n.divisors) => hd d)
  have he : (∑ d ∈ n.divisors, -(μ d : ℝ) * Real.log d) = Λ n := by
    simp_rw [neg_mul, sum_neg_distrib]
    simpa only [log_apply, neg_neg] using congrArg Neg.neg (sum_moebius_mul_log_eq (n := n))
  rw [he] at hh
  exact hh

/-- This is a pointwise limit for each fixed input. -/
theorem smoothMangoldt_tendsto (n : ℕ) :
    Tendsto (fun t : ℝ => smoothMangoldt t n) (𝓝[>] 0) (𝓝 (Λ n)) := by
  have hh := (hasDerivAt_expDivisorSum n).tendsto_slope_zero_right
  simpa only [smoothMangoldt, zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

lemma expDivisorSum_remainder_identity (t : ℝ) (n : ℕ) :
    expDivisorSum t n - expDivisorSum 0 n - t * Λ n =
      ∑ d ∈ n.divisors, (μ d : ℝ) *
        (Real.exp (-t * Real.log d) - 1 + t * Real.log d) := by
  have hh := sum_moebius_mul_log_eq (n := n)
  simp only [log_apply] at hh
  simp only [expDivisorSum, neg_zero, zero_mul, Real.exp_zero, mul_one,
    mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  have he : (∑ d ∈ n.divisors, (μ d : ℝ) * (t * Real.log d)) =
      t * ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d := by
    rw [mul_sum]
    apply sum_congr rfl
    intro d hd
    ring
  rw [he, hh]
  ring

/-- A quantitative finite-window estimate. The divisor-cardinality factor is
retained; this is not an asymptotic correlation estimate. -/
theorem smoothMangoldt_error_bound {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hsmall : t * Real.log n ≤ 1) :
    |smoothMangoldt t n - Λ n| ≤ t * n.divisors.card * (Real.log n)^2 := by
  by_cases hn : n = 0
  · simp [hn, smoothMangoldt, expDivisorSum]
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlogn := Real.log_natCast_nonneg n
  have hlocal (d : ℕ) (hd : d ∈ n.divisors) :
      |(μ d : ℝ) * (Real.exp (-t * Real.log d) - 1 + t * Real.log d)| ≤
        t^2 * (Real.log n)^2 := by
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)
    have hlogd := Real.log_natCast_nonneg d
    have hlogdn := Real.log_le_log (Nat.cast_pos.mpr hd0) (Nat.cast_le.mpr hdn)
    have htn : 0 ≤ t * Real.log d := mul_nonneg ht.le hlogd
    have htd : t * Real.log d ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlogdn ht.le).trans hsmall
    have he := Real.norm_exp_sub_one_sub_id_le
      (x := -t * Real.log d) (by
        rw [Real.norm_eq_abs, neg_mul, abs_neg, abs_of_nonneg htn]
        exact htd)
    simp only [Real.norm_eq_abs, neg_mul, sub_neg_eq_add, abs_neg,
      abs_of_nonneg htn, mul_pow] at he
    rw [abs_mul, neg_mul]
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
    calc
      _ ≤ 1 * (t^2 * (Real.log d)^2) :=
        mul_le_mul hμ he (abs_nonneg _) (by norm_num)
      _ ≤ t^2 * (Real.log n)^2 := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogd hlogdn 2) (sq_nonneg t)
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hlocal)
  rw [← expDivisorSum_remainder_identity] at hsum
  simp only [sum_const, nsmul_eq_mul] at hsum
  have heq : smoothMangoldt t n - Λ n =
      (expDivisorSum t n - expDivisorSum 0 n - t * Λ n) / t := by
    unfold smoothMangoldt
    field_simp
  rw [heq, abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  nlinarith only [hsum]

/-- Correlation convergence on a fixed finite input window. This theorem
cannot be used with a window depending on t without further estimates. -/
theorem finite_smooth_correlation_tendsto (α : ℝ) (N : ℕ) :
    Tendsto (fun t : ℝ => ∑ n ∈ Ioc 0 N,
      smoothMangoldt t n * smoothMangoldt t (floorMul α n))
      (𝓝[>] 0) (𝓝 (mangoldtCorrelation α N)) := by
  exact tendsto_finset_sum _ (fun n _ =>
    (smoothMangoldt_tendsto n).mul (smoothMangoldt_tendsto (floorMul α n)))

#print axioms smoothMangoldt_tendsto
#print axioms smoothMangoldt_error_bound
#print axioms finite_smooth_correlation_tendsto

end Erdos972SmoothMangoldt
