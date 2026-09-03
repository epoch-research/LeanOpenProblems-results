import Submission.SignedSmoothMinorant

/-! A size-dependent two-scale minorant valid for every positive smoothing
parameter. No positive mean of this signed minorant is asserted. -/
namespace Erdos972GlobalTwoScaleMinorant

open Finset ArithmeticFunction
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SignedSmoothMinorant

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def halfDamping (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(t / 2) * Real.log n)

noncomputable def globalMinorant (t : ℝ) (n : ℕ) : ℝ :=
  if n = 1 then 0 else
    ((1 + halfDamping t n)^2 * expDivisorSum t n - expDivisorSum (2*t) n) /
      (2*t*halfDamping t n)

lemma halfDamping_pos (t : ℝ) (n : ℕ) : 0 < halfDamping t n :=
  Real.exp_pos _

lemma halfDamping_sq (t : ℝ) (n : ℕ) :
    (halfDamping t n)^2 = Real.exp (-t * Real.log n) := by
  rw [halfDamping, pow_two, ← Real.exp_add]
  congr 1
  ring

lemma doubling_product_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn : ¬ IsPrimePow n) :
    (1 + halfDamping t n)^2 ≤
      ∏ p ∈ n.primeFactors, (1 + Real.exp (-t * Real.log p)) := by
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
  have hlogs : Real.log p + Real.log q ≤ Real.log n := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hpp.pos hqp.pos))
      (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpqd))
    rwa [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hpp.ne_zero)
      (Nat.cast_ne_zero.mpr hqp.ne_zero)] at hh
  have hprod : (halfDamping t n)^2 ≤
      Real.exp (-t*Real.log p) * Real.exp (-t*Real.log q) := by
    rw [halfDamping_sq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlogs ht.le]
  have hsum : 2*halfDamping t n ≤
      Real.exp (-t*Real.log p) + Real.exp (-t*Real.log q) := by
    apply (sq_le_sq₀ (by positivity [halfDamping_pos t n]) (by positivity)).mp
    nlinarith only [hprod, sq_nonneg (Real.exp (-t*Real.log p) - Real.exp (-t*Real.log q))]
  have hpair : (1+halfDamping t n)^2 ≤
      (1+Real.exp (-t*Real.log p))*(1+Real.exp (-t*Real.log q)) := by
    nlinarith only [hprod, hsum]
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

theorem nonPrimePower_nonpos {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : ¬ IsPrimePow n) : globalMinorant t n ≤ 0 := by
  by_cases hn0 : n = 0
  · simp [hn0, globalMinorant, expDivisorSum]
  by_cases hn1 : n = 1
  · simp [hn1, globalMinorant]
  have hprod := doubling_product_lower ht hn0 hn1 hn
  have he := mul_le_mul_of_nonneg_left hprod (expDivisorSum_nonneg ht.le n)
  have hnum : (1+halfDamping t n)^2 * expDivisorSum t n - expDivisorSum (2*t) n ≤ 0 := by
    rw [expDivisorSum_double t hn0]
    nlinarith only [he]
  rw [globalMinorant, if_neg hn1]
  exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity [halfDamping_pos t n])

lemma primePower_identity {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : IsPrimePow n) :
    globalMinorant t n = smoothMangoldt t n +
      expDivisorSum t n * (Real.exp (-t*Real.log n) - Real.exp (-t*Λ n)) /
        (2*t*halfDamping t n) := by
  have hn1 := hn.ne_one
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [globalMinorant, if_neg hn1, smoothMangoldt, expDivisorSum_at_zero,
    one_apply, if_neg hn1, sub_zero, expDivisorSum_prime_pow t hp hk,
    expDivisorSum_prime_pow (2*t) hp hk, vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hp, exp_double]
  have hz := halfDamping_sq t (p^k)
  have hz0 := (halfDamping_pos t (p^k)).ne'
  field_simp
  simp only [neg_mul] at hz
  rw [← hz]
  ring

lemma primePower_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : IsPrimePow n) :
    globalMinorant t n ≤ smoothMangoldt t n := by
  rw [primePower_identity ht hn]
  have hlog : Λ n ≤ Real.log n := vonMangoldt_le_log
  have he : Real.exp (-t*Real.log n) ≤ Real.exp (-t*Λ n) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlog ht.le]
  have hnum := mul_nonpos_of_nonneg_of_nonpos (expDivisorSum_nonneg ht.le n)
    (sub_nonpos.mpr he)
  have hd := div_nonpos_of_nonpos_of_nonneg hnum
    (by positivity [halfDamping_pos t n] : 0 ≤ 2*t*halfDamping t n)
  linarith only [hd]

/-- This minorant has no restriction on `t * log n`. Proper prime powers
are still handled by Mangoldt, rather than being identified with primes. -/
theorem globalMinorant_le_mangoldt {t : ℝ} (ht : 0 < t) (n : ℕ) :
    globalMinorant t n ≤ Λ n := by
  by_cases hn : IsPrimePow n
  · exact (primePower_le ht hn).trans (smoothMangoldt_primePower_le ht hn)
  · exact (nonPrimePower_nonpos ht hn).trans vonMangoldt_nonneg

/-- At a genuine prime the new minorant equals the original positive proxy. -/
theorem globalMinorant_prime {t : ℝ} (ht : 0 < t) {p : ℕ} (hp : p.Prime) :
    globalMinorant t p = smoothMangoldt t p := by
  rw [primePower_identity ht hp.isPrimePow, vonMangoldt_apply_prime hp]
  simp

#print axioms doubling_product_lower
#print axioms globalMinorant_le_mangoldt
#print axioms globalMinorant_prime

end Erdos972GlobalTwoScaleMinorant
