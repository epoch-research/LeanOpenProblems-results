import Submission.SmoothCorrelationApprox

/-! A divisor-cardinality-free bound for the full smoothed Mangoldt error.
Prime powers are handled by a one-factor exponential estimate; all other
positive nonunits have at least two distinct prime factors. -/
namespace Erdos972SharpSmoothMangoldt

open Finset ArithmeticFunction
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive

lemma exp_slope_error {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    |(1-Real.exp (-t*x))/t-x| ≤ t*x^2 := by
  have hx0 : 0 ≤ t*x := mul_nonneg ht.le hx
  have hupper : (1-Real.exp (-t*x))/t ≤ x := by
    apply (div_le_iff₀ ht).mpr
    linarith only [Real.add_one_le_exp (-t*x)]
  have hlower : 0 ≤ (1-Real.exp (-t*x))/t := by
    apply div_nonneg _ ht.le
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith only [hx0]))
  by_cases hsmall : t*x ≤ 1
  · have he := Real.norm_exp_sub_one_sub_id_le (x := -t*x) (by
      rw [Real.norm_eq_abs, neg_mul, abs_neg, abs_of_nonneg hx0]
      exact hsmall)
    simp only [Real.norm_eq_abs, neg_mul, sub_neg_eq_add, abs_neg,
      abs_of_nonneg hx0, mul_pow] at he
    have hid : (1-Real.exp (-t*x))/t-x = -(Real.exp (-(t*x))-1+t*x)/t := by field_simp; ring
    rw [hid, abs_div, abs_neg, abs_of_pos ht]
    apply (div_le_iff₀ ht).mpr
    nlinarith only [he]
  · rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
    have hh := mul_le_mul_of_nonneg_right (le_of_not_ge hsmall) hx
    nlinarith only [hh, hlower]

lemma smoothMangoldt_primePower_error {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : IsPrimePow n) :
    |smoothMangoldt t n-Λ n| ≤ t*(Real.log n)^2 := by
  have hn1 := hn.ne_one
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have hlog : Real.log p ≤ Real.log (p^k : ℕ) := Real.log_le_log
    (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr (Nat.le_pow hk))
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero,
    expDivisorSum_prime_pow t hp hk, vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
  exact (exp_slope_error ht (Real.log_natCast_nonneg p)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_natCast_nonneg p) hlog 2) ht.le)

lemma expDivisorSum_le_two_factors {t : ℝ} (ht : 0 ≤ t) {n p q : ℕ}
    (hn : n ≠ 0) (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) (hpq : p ≠ q) :
    expDivisorSum t n ≤
      (1-Real.exp (-t*Real.log p))*(1-Real.exp (-t*Real.log q)) := by
  classical
  have hqe : q ∈ n.primeFactors.erase p := mem_erase.mpr ⟨hpq.symm, hq⟩
  rw [expDivisorSum_product t hn,
    ← prod_erase_mul n.primeFactors (fun r : ℕ => 1-Real.exp (-t*Real.log r)) hp,
    ← prod_erase_mul (n.primeFactors.erase p) (fun r : ℕ => 1-Real.exp (-t*Real.log r)) hqe]
  have hh : (∏ r ∈ (n.primeFactors.erase p).erase q, (1-Real.exp (-t*Real.log r))) ≤ 1 :=
    prod_le_one (fun r _ => expFactor_nonneg ht r) (fun r _ => expFactor_le_one t r)
  have hbound := mul_le_mul_of_nonneg_right hh
    (mul_nonneg (expFactor_nonneg ht q) (expFactor_nonneg ht p))
  nlinarith only [hbound]

lemma smoothMangoldt_nonPrimePower_bound {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : ¬ IsPrimePow n) : smoothMangoldt t n ≤ t*(Real.log n)^2 := by
  by_cases hn0 : n = 0
  · simp [hn0, smoothMangoldt, expDivisorSum]
  by_cases hn1 : n = 1
  · simp [hn1, smoothMangoldt, expDivisorSum]
  have hcardpos : 0 < n.primeFactors.card := card_pos.mpr
    (Nat.nonempty_primeFactors.mpr (by omega))
  have hcardne : n.primeFactors.card ≠ 1 := fun h => hn (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp (show 1 < n.primeFactors.card by omega)
  have hlogp : Real.log p ≤ Real.log n := Real.log_le_log
    (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos)
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)))
  have hlogq : Real.log q ≤ Real.log n := Real.log_le_log
    (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos)
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hq)))
  have hpbound : 1-Real.exp (-t*Real.log p) ≤ t*Real.log n := by
    have he := Real.add_one_le_exp (-t*Real.log p)
    have hm := mul_le_mul_of_nonneg_left hlogp ht.le
    linarith only [he, hm]
  have hqbound : 1-Real.exp (-t*Real.log q) ≤ t*Real.log n := by
    have he := Real.add_one_le_exp (-t*Real.log q)
    have hm := mul_le_mul_of_nonneg_left hlogq ht.le
    linarith only [he, hm]
  have hprod := (expDivisorSum_le_two_factors ht.le hn0 hp hq hpq).trans
    (mul_le_mul hpbound hqbound (expFactor_nonneg ht.le q) (by positivity [Real.log_natCast_nonneg n]))
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero]
  apply (div_le_iff₀ ht).mpr
  nlinarith only [hprod]

/-- Global pointwise error: no divisor-count factor and no smallness
hypothesis on t*log(n). -/
theorem smoothMangoldt_error_sharp {t : ℝ} (ht : 0 < t) (n : ℕ) :
    |smoothMangoldt t n-Λ n| ≤ t*(Real.log n)^2 := by
  by_cases hn : IsPrimePow n
  · exact smoothMangoldt_primePower_error ht hn
  · rw [vonMangoldt_eq_zero_iff.mpr hn, sub_zero, abs_of_nonneg (smoothMangoldt_nonneg ht n)]
    exact smoothMangoldt_nonPrimePower_bound ht hn

#print axioms smoothMangoldt_error_sharp

end Erdos972SharpSmoothMangoldt
