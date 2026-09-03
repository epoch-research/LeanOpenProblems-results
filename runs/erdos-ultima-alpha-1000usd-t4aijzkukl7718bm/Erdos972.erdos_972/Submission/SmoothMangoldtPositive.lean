import Submission.SmoothMangoldt

/-! Euler-product positivity and a pointwise logarithmic bound for the
exponential-divisor approximation. These bounds do not establish any
uniform mean-value estimate as the smoothing parameter tends to zero. -/
namespace Erdos972SmoothMangoldtPositive

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972SmoothMangoldt

noncomputable def expWeight (t : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else Real.exp (-t * Real.log n), by simp⟩

lemma isMultiplicative_expWeight (t : ℝ) : (expWeight t).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [expWeight], ?_⟩
  intro m n hm hn _
  simp only [expWeight, coe_mk, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
    Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn),
    mul_add, Real.exp_add]

lemma expDivisorSum_eq (t : ℝ) (n : ℕ) :
    expDivisorSum t n = ((ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) (expWeight t)) * ζ) n := by
  rw [coe_mul_zeta_apply]
  apply sum_congr rfl
  intro d hd
  simp only [pmul_apply, intCoe_apply, expWeight, coe_mk,
    if_neg (Nat.pos_of_mem_divisors hd).ne']

lemma expDivisorSum_prime_pow (t : ℝ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    expDivisorSum t (p^k) = 1 - Real.exp (-t * Real.log p) := by
  rw [expDivisorSum, Nat.sum_divisors_prime_pow hp, sum_range_succ']
  have hterm (i : ℕ) : (μ (p^(i+1)) : ℝ) * Real.exp (-t * Real.log (p^(i+1):ℕ)) =
      if i = 0 then -Real.exp (-t * Real.log p) else 0 := by
    by_cases hi : i = 0
    · subst i
      simp [moebius_apply_prime hp]
    · rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
      simp [hi]
  simp_rw [hterm]
  simp [hk]
  ring

/-- The divisor sum is the usual product over the distinct prime divisors.
The n=0 convention is excluded explicitly. -/
theorem expDivisorSum_product (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    expDivisorSum t n = ∏ p ∈ n.primeFactors, (1 - Real.exp (-t * Real.log p)) := by
  let f : ArithmeticFunction ℝ := (ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) (expWeight t)) * ζ
  have hf : f.IsMultiplicative :=
    (isMultiplicative_moebius.intCast.pmul (isMultiplicative_expWeight t)).mul
      isMultiplicative_zeta.natCast
  rw [expDivisorSum_eq]
  change f n = _
  rw [hf.multiplicative_factorization f hn]
  unfold Finsupp.prod
  rw [Nat.support_factorization]
  apply prod_congr rfl
  intro p hp
  change ((ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) (expWeight t)) * ζ)
    (p ^ n.factorization p) = _
  rw [← expDivisorSum_eq]
  apply expDivisorSum_prime_pow t (Nat.prime_of_mem_primeFactors hp)
  apply Nat.pos_of_ne_zero
  exact Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)

lemma expFactor_nonneg {t : ℝ} (ht : 0 ≤ t) (p : ℕ) :
    0 ≤ 1 - Real.exp (-t * Real.log p) := by
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Real.log_natCast_nonneg p)

lemma expFactor_le_one (t : ℝ) (p : ℕ) : 1 - Real.exp (-t * Real.log p) ≤ 1 := by
  linarith [Real.exp_nonneg (-t * Real.log p)]

lemma expDivisorSum_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ expDivisorSum t n := by
  by_cases hn : n = 0
  · simp [hn, expDivisorSum]
  rw [expDivisorSum_product t hn]
  exact prod_nonneg fun p _ => expFactor_nonneg ht p

/-- The approximation is genuinely nonnegative, including at n=0 and n=1. -/
theorem smoothMangoldt_nonneg {t : ℝ} (ht : 0 < t) (n : ℕ) :
    0 ≤ smoothMangoldt t n := by
  by_cases hn : n = 1
  · simp [hn, smoothMangoldt, expDivisorSum]
  rw [smoothMangoldt, expDivisorSum_at_zero]
  simp only [one_apply, if_neg hn, sub_zero]
  exact div_nonneg (expDivisorSum_nonneg ht.le n) ht.le

/-- A bound uniform in the smoothing parameter, not in the correlation
mean-value limit. -/
theorem smoothMangoldt_le_log {t : ℝ} (ht : 0 < t) (n : ℕ) :
    smoothMangoldt t n ≤ Real.log n := by
  by_cases hn0 : n = 0
  · simp [hn0, smoothMangoldt, expDivisorSum]
  by_cases hn1 : n = 1
  · simp [hn1, smoothMangoldt, expDivisorSum]
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime hn1
  have hpn : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, hn0⟩
  have hprod : (∏ q ∈ n.primeFactors, (1 - Real.exp (-t * Real.log q))) ≤
      1 - Real.exp (-t * Real.log p) := by
    rw [← prod_erase_mul n.primeFactors (fun q : ℕ => 1 - Real.exp (-t * Real.log q)) hpn]
    have hh : (∏ q ∈ n.primeFactors.erase p, (1 - Real.exp (-t * Real.log q))) ≤ 1 :=
      prod_le_one (fun q _ => expFactor_nonneg ht.le q) (fun q _ => expFactor_le_one t q)
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hh (expFactor_nonneg ht.le p)
  have hfactor : 1 - Real.exp (-t * Real.log p) ≤ t * Real.log p := by
    linarith [Real.add_one_le_exp (-t * Real.log p)]
  have hlog : Real.log p ≤ Real.log n := Real.log_le_log (Nat.cast_pos.mpr hp.pos)
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.minFac_dvd n)))
  rw [smoothMangoldt, expDivisorSum_at_zero]
  simp only [one_apply, if_neg hn1, sub_zero]
  apply (div_le_iff₀ ht).mpr
  rw [expDivisorSum_product t hn0]
  exact (hprod.trans hfactor).trans (by nlinarith only [mul_le_mul_of_nonneg_left hlog ht.le])

#print axioms expDivisorSum_product
#print axioms smoothMangoldt_nonneg
#print axioms smoothMangoldt_le_log

end Erdos972SmoothMangoldtPositive
