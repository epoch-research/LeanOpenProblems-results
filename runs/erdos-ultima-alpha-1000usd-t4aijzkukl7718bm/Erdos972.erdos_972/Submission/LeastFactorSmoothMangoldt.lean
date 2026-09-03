import Submission.SharpSmoothMangoldt

/-! The full smoothed Mangoldt error can retain the least prime factor.
This does not assert a lower bound for a prime-pair correlation. -/
namespace Erdos972LeastFactorSmoothMangoldt

open Finset ArithmeticFunction
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive Erdos972SharpSmoothMangoldt

lemma primePower_error_leastFactor {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : IsPrimePow n) :
    |smoothMangoldt t n - Λ n| ≤ t * Real.log n * Real.log n.minFac := by
  have hn1 := hn.ne_one
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have hlo : Real.log p ≤ Real.log (p^k : ℕ) := Real.log_le_log
    (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr (Nat.le_pow hk))
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero,
    expDivisorSum_prime_pow t hp hk, vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hp, hp.pow_minFac hk.ne']
  apply (exp_slope_error ht (Real.log_natCast_nonneg p)).trans
  have hh := mul_le_mul_of_nonneg_right hlo
    (mul_nonneg ht.le (Real.log_natCast_nonneg p))
  nlinarith only [hh]

lemma nonPrimePower_bound_leastFactor {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : ¬ IsPrimePow n) :
    smoothMangoldt t n ≤ t * Real.log n * Real.log n.minFac := by
  by_cases hn0 : n = 0
  · simp [hn0, smoothMangoldt, expDivisorSum]
  by_cases hn1 : n = 1
  · simp [hn1, smoothMangoldt, expDivisorSum]
  have hp : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hn0
  have hcardpos : 0 < n.primeFactors.card := card_pos.mpr ⟨_, hp⟩
  have hcardne : n.primeFactors.card ≠ 1 :=
    fun h => hn (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
  obtain ⟨q, hq, hqp⟩ := exists_mem_ne (show 1 < n.primeFactors.card by omega) n.minFac
  have hlogq : Real.log q ≤ Real.log n := Real.log_le_log
    (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos)
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
      (Nat.dvd_of_mem_primeFactors hq)))
  have hpbound : 1 - Real.exp (-t * Real.log n.minFac) ≤ t * Real.log n.minFac := by
    linarith only [Real.add_one_le_exp (-t * Real.log n.minFac)]
  have hqbound : 1 - Real.exp (-t * Real.log q) ≤ t * Real.log n := by
    have h := mul_le_mul_of_nonneg_left hlogq ht.le
    linarith only [h, Real.add_one_le_exp (-t * Real.log q)]
  have hprod := (expDivisorSum_le_two_factors ht.le hn0 hp hq hqp.symm).trans
    (mul_le_mul hpbound hqbound (expFactor_nonneg ht.le q)
      (mul_nonneg ht.le (Real.log_natCast_nonneg n.minFac)))
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero]
  apply (div_le_iff₀ ht).mpr
  nlinarith only [hprod]

/-- A least-factor refinement of the divisor-cardinality-free error bound.
It holds for every n and every positive damping parameter. -/
theorem smoothMangoldt_error_leastFactor {t : ℝ} (ht : 0 < t) (n : ℕ) :
    |smoothMangoldt t n - Λ n| ≤ t * Real.log n * Real.log n.minFac := by
  by_cases hn : IsPrimePow n
  · exact primePower_error_leastFactor ht hn
  · rw [vonMangoldt_eq_zero_iff.mpr hn, sub_zero,
      abs_of_nonneg (smoothMangoldt_nonneg ht n)]
    exact nonPrimePower_bound_leastFactor ht hn

/-- A mixed weighted comparison. Estimating the final least-factor moment
is separate from proving a lower bound for the smoothed sum. -/
theorem weighted_smooth_error (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    {t L : ℝ} (ht : 0 < t)
    (ha : ∀ n ∈ S, 0 ≤ a n) (hlog : ∀ n ∈ S, Real.log (g n) ≤ L) :
    |(∑ n ∈ S, a n * smoothMangoldt t (g n)) -
      (∑ n ∈ S, a n * Λ (g n))| ≤
      t * L * ∑ n ∈ S, a n * Real.log (g n).minFac := by
  rw [← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [← mul_sub, abs_mul, abs_of_nonneg (ha n hn)]
  have he := mul_le_mul_of_nonneg_left (smoothMangoldt_error_leastFactor ht (g n))
    (ha n hn)
  have hl := mul_le_mul_of_nonneg_left (hlog n hn)
    (show 0 ≤ a n * t * Real.log (g n).minFac by
      exact mul_nonneg (mul_nonneg (ha n hn) ht.le) (Real.log_natCast_nonneg _))
  nlinarith only [he, hl]

#print axioms smoothMangoldt_error_leastFactor
#print axioms weighted_smooth_error

end Erdos972LeastFactorSmoothMangoldt
