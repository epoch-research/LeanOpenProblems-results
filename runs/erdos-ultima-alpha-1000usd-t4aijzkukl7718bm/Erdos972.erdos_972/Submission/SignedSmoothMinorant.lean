import Submission.SharpSmoothMangoldt

/-! A two-scale signed smoothing minorant. In a finite small-parameter
window its positive support is exactly the prime powers. No positive
prime-weighted mean of this signed function is asserted here. -/
namespace Erdos972SignedSmoothMinorant

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SharpSmoothMangoldt

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def signedSmooth (t : ℝ) (n : ℕ) : ℝ :=
  smoothMangoldt t n-smoothMangoldt (2*t) n

lemma exp_double (t x : ℝ) :
    Real.exp (-(2*t)*x) = (Real.exp (-t*x))^2 := by
  rw [show -(2*t)*x = (-t*x)+(-t*x) by ring, Real.exp_add, pow_two]

lemma expDivisorSum_double (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    expDivisorSum (2*t) n = expDivisorSum t n *
      ∏ p ∈ n.primeFactors, (1+Real.exp (-t*Real.log p)) := by
  rw [expDivisorSum_product _ hn, expDivisorSum_product _ hn, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  rw [exp_double]
  ring

lemma doubling_product_ge_two {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn : ¬ IsPrimePow n)
    (hsmall : t*Real.log n ≤ 1) :
    2 ≤ ∏ p ∈ n.primeFactors, (1+Real.exp (-t*Real.log p)) := by
  classical
  have hc0 : 0 < n.primeFactors.card := card_pos.mpr
    (Nat.nonempty_primeFactors.mpr (by omega))
  have hc1 : n.primeFactors.card ≠ 1 := fun h =>
    hn (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp (show 1 < n.primeFactors.card by omega)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hpqd : p*q ∣ n := ((Nat.coprime_primes hpp hqp).mpr hpq).mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq)
  have hlogs : Real.log p+Real.log q ≤ Real.log n := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hpp.pos hqp.pos))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpqd))
    rwa [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hpp.ne_zero)
      (Nat.cast_ne_zero.mpr hqp.ne_zero)] at hh
  have hm := mul_le_mul_of_nonneg_left hlogs ht.le
  have he := Real.add_one_le_exp (-t*Real.log p)
  have hf := Real.add_one_le_exp (-t*Real.log q)
  have hpair : 2 ≤ (1+Real.exp (-t*Real.log p))*(1+Real.exp (-t*Real.log q)) := by
    have hpos := mul_nonneg (Real.exp_nonneg (-t*Real.log p))
      (Real.exp_nonneg (-t*Real.log q))
    nlinarith only [hm, hsmall, he, hf, hpos]
  have hqe : q ∈ n.primeFactors.erase p := mem_erase.mpr ⟨hpq.symm, hq⟩
  rw [← prod_erase_mul n.primeFactors (fun r : ℕ => 1+Real.exp (-t*Real.log r)) hp,
    ← prod_erase_mul (n.primeFactors.erase p) (fun r : ℕ => 1+Real.exp (-t*Real.log r)) hqe]
  have hrest : 1 ≤ ∏ r ∈ (n.primeFactors.erase p).erase q,
      (1+Real.exp (-t*Real.log r)) :=
    one_le_prod _ (fun r => by linarith only [Real.exp_nonneg (-t*Real.log r)])
  have hh := mul_le_mul_of_nonneg_right hrest
    (mul_nonneg (by positivity : 0 ≤ 1+Real.exp (-t*Real.log p))
      (by positivity : 0 ≤ 1+Real.exp (-t*Real.log q)))
  nlinarith only [hh, hpair]

/-- Non-prime-powers make a nonpositive contribution in the stated window. -/
theorem signedSmooth_nonPrimePower_nonpos {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : ¬ IsPrimePow n) (hsmall : t*Real.log n ≤ 1) : signedSmooth t n ≤ 0 := by
  by_cases hn0 : n = 0
  · simp [hn0, signedSmooth, smoothMangoldt, expDivisorSum]
  by_cases hn1 : n = 1
  · simp [hn1, signedSmooth, smoothMangoldt, expDivisorSum]
  have hprod := doubling_product_ge_two ht hn0 hn1 hn hsmall
  have he := mul_le_mul_of_nonneg_left hprod (expDivisorSum_nonneg ht.le n)
  rw [← expDivisorSum_double t hn0] at he
  rw [signedSmooth, smoothMangoldt, smoothMangoldt, expDivisorSum_at_zero,
    one_apply, if_neg hn1, sub_zero, sub_zero]
  have h₂ : 0 < 2*t := by positivity
  have hh : expDivisorSum t n/t ≤ expDivisorSum (2*t) n/(2*t) := by
    apply (div_le_div_iff₀ ht h₂).mpr
    have h := mul_le_mul_of_nonneg_right he ht.le
    nlinarith only [h]
  linarith only [hh]

/-- Exact positive prime-power contribution; proper powers are not silently
identified with primes. -/
theorem signedSmooth_primePower {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : IsPrimePow n) :
    signedSmooth t n = (1-Real.exp (-t*Λ n))^2/(2*t) := by
  have hn1 := hn.ne_one
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [signedSmooth, smoothMangoldt, smoothMangoldt, expDivisorSum_at_zero,
    one_apply, if_neg hn1, sub_zero, sub_zero, expDivisorSum_prime_pow t hp hk,
    expDivisorSum_prime_pow (2*t) hp hk, vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hp, exp_double]
  field_simp
  ring

lemma smoothMangoldt_primePower_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : IsPrimePow n) :
    smoothMangoldt t n ≤ Λ n := by
  have hn1 := hn.ne_one
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hn1, sub_zero,
    expDivisorSum_prime_pow t hp hk, vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hp]
  apply (div_le_iff₀ ht).mpr
  linarith only [Real.add_one_le_exp (-t*Real.log p)]

theorem signedSmooth_le_mangoldt {t : ℝ} (ht : 0 < t) (n : ℕ)
    (hsmall : t*Real.log n ≤ 1) : signedSmooth t n ≤ Λ n := by
  by_cases hn : IsPrimePow n
  · have hs := smoothMangoldt_nonneg (show 0 < 2*t by positivity) n
    have hp := smoothMangoldt_primePower_le ht hn
    unfold signedSmooth
    linarith only [hs, hp]
  · exact (signedSmooth_nonPrimePower_nonpos ht hn hsmall).trans vonMangoldt_nonneg

/-- The positive support, not the full support, is exactly the prime powers. -/
theorem signedSmooth_pos_iff {t : ℝ} (ht : 0 < t) (n : ℕ)
    (hsmall : t*Real.log n ≤ 1) : 0 < signedSmooth t n ↔ IsPrimePow n := by
  constructor
  · intro hp
    by_contra hn
    exact (not_lt_of_ge (signedSmooth_nonPrimePower_nonpos ht hn hsmall)) hp
  · intro hn
    rw [signedSmooth_primePower ht hn]
    have hΛ : 0 < Λ n := vonMangoldt_pos_iff.mpr hn
    have he : Real.exp (-t*Λ n) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos ht hΛ])
    exact div_pos (sq_pos_of_pos (sub_pos.mpr he)) (by positivity)

/-- This identity retains the signed Mobius coefficients. Replacing them by
absolute values is not a positive mean-value estimate. -/
theorem signedSmooth_divisor_identity {t : ℝ} (ht : 0 < t) (n : ℕ) :
    signedSmooth t n = -(∑ d ∈ n.divisors,
      (μ d:ℝ)*(1-Real.exp (-t*Real.log d))^2)/(2*t) := by
  have he : (∑ d ∈ n.divisors, (μ d:ℝ)*(1-Real.exp (-t*Real.log d))^2) =
      expDivisorSum (2*t) n-2*expDivisorSum t n+expDivisorSum 0 n := by
    simp only [expDivisorSum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    rw [exp_double]
    simp only [neg_zero, zero_mul, Real.exp_zero]
    ring
  rw [he, signedSmooth, smoothMangoldt, smoothMangoldt]
  field_simp
  ring

/-- The original decaying divisor coefficient has only a constant-factor
change; the two-scale subtraction does not give stronger exponential damping. -/
lemma signed_coefficient_bounds {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x)/2 ≤ Real.exp (-x)-Real.exp (-2*x)/2 ∧
      Real.exp (-x)-Real.exp (-2*x)/2 ≤ Real.exp (-x) := by
  have he : Real.exp (-2*x) = (Real.exp (-x))^2 := by
    simpa only [one_mul, mul_one, neg_mul, neg_neg] using exp_double 1 x
  have h0 := Real.exp_nonneg (-x)
  have h1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  rw [he]
  constructor <;> nlinarith only [h0, h1, sq_nonneg (Real.exp (-x)),
    mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- A finite signed minorant comparison. There is no claim that the left
side is positive for the prime-input weights of the conjecture. -/
theorem weighted_signed_minorant (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    {t : ℝ} (ht : 0 < t) (ha : ∀ n ∈ S, 0 ≤ a n)
    (hsmall : ∀ n ∈ S, t*Real.log (g n) ≤ 1) :
    (∑ n ∈ S, a n*signedSmooth t (g n)) ≤ ∑ n ∈ S, a n*Λ (g n) := by
  apply sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left (signedSmooth_le_mangoldt ht (g n) (hsmall n hn)) (ha n hn)

#print axioms signedSmooth_nonPrimePower_nonpos
#print axioms signedSmooth_primePower
#print axioms signedSmooth_le_mangoldt
#print axioms signedSmooth_pos_iff
#print axioms signedSmooth_divisor_identity
#print axioms signed_coefficient_bounds
#print axioms weighted_signed_minorant

end Erdos972SignedSmoothMinorant
