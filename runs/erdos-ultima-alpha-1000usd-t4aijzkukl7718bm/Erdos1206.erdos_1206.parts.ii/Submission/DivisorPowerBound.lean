import FormalConjecturesUtil

/-! An elementary power bound for the divisor function, with explicit constants. -/
namespace Erdos1206.DivisorPowerBound
open Finset

private lemma polynomial_le_exp (k e : ℕ) :
    (e+1)^k ≤ (k.factorial*2^k)*2^e := by
  calc
    (e+1)^k ≤ (e+1).ascFactorial k := Nat.pow_succ_le_ascFactorial _ _
    _ = k.factorial*(e+k).choose k := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ k.factorial*2^(e+k) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by rw [pow_add]; ring

private lemma large_prime_bound {k p : ℕ} (hp : 2^k ≤ p) (e : ℕ) :
    (e+1)^k ≤ p^e := by
  calc
    (e+1)^k ≤ (2^e)^k := Nat.pow_le_pow_left (by have := Nat.lt_two_pow_self (n := e); omega) _
    _ = (2^k)^e := by rw [←pow_mul,←pow_mul,Nat.mul_comm e k]
    _ ≤ p^e := Nat.pow_le_pow_left hp _

def constant (k : ℕ) : ℕ := (k.factorial*2^k)^(2^k)

lemma constant_pos (k : ℕ) : 0 < constant k := by
  dsimp [constant]
  exact pow_pos (Nat.mul_pos (Nat.factorial_pos _) (by positivity)) _

/-- For every fixed positive exponent, the corresponding power of the divisor
count is bounded by a constant times the integer itself. -/
theorem card_divisors_pow_le (k : ℕ) {n : ℕ} (hn : 0 < n) :
    n.divisors.card^k ≤ constant k*n := by
  classical
  let K := k.factorial*2^k
  have hK : 0 < K := Nat.mul_pos (Nat.factorial_pos _) (by positivity)
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p+1)^k ≤ (if p < 2^k then K else 1)*p^(n.factorization p) := by
    by_cases hsmall : p < 2^k
    · rw [if_pos hsmall]
      exact (polynomial_le_exp k _).trans
        (Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _))
    · rw [if_neg hsmall,one_mul]
      exact large_prime_bound (by omega) _
  have hc : (n.primeFactors.filter (fun p => p < 2^k)).card ≤ 2^k := by
    calc
      _ ≤ (range (2^k)).card := card_le_card (by intro p hp; exact mem_range.mpr (mem_filter.mp hp).2)
      _ = _ := card_range _
  have hprod : (∏ p ∈ n.primeFactors, (if p < 2^k then K else 1)) ≤ constant k := by
    rw [←prod_filter,prod_const]
    exact Nat.pow_le_pow_right hK hc
  have hfactor : (∏ p ∈ n.primeFactors, p^(n.factorization p))=n := by
    rw [←Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.factorization_prod_pow_eq_self hn.ne'
  calc
    _ = ∏ p ∈ n.primeFactors, (n.factorization p+1)^k := by
      rw [Nat.card_divisors hn.ne',prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < 2^k then K else 1)*p^(n.factorization p) := prod_le_prod' hlocal
    _ = (∏ p ∈ n.primeFactors, (if p < 2^k then K else 1))*n := by
      rw [prod_mul_distrib,hfactor]
    _ ≤ constant k*n := Nat.mul_le_mul_right _ hprod

/-- Integer-power cutoffs avoid any need for real fractional powers. -/
theorem card_divisors_le_at_power_cutoff {n t : ℕ} (hn : 0 < n)
    (hbound : n ≤ 2*t^36) : n.divisors.card ≤ (2*constant 12+1)*t^3 := by
  have hpow := (card_divisors_pow_le 12 hn).trans (Nat.mul_le_mul_left (constant 12) hbound)
  apply (Nat.pow_le_pow_iff_left (by decide : (12:ℕ)≠0)).mp
  have hC : 2*constant 12 ≤ (2*constant 12+1)^12 := by
    have hh := Nat.le_self_pow (by decide : 12≠0) (2*constant 12+1)
    omega
  calc
    _ ≤ constant 12*(2*t^36) := hpow
    _ ≤ (2*constant 12+1)^12*t^36 := by nlinarith [Nat.mul_le_mul_right (t^36) hC]
    _ = ((2*constant 12+1)*t^3)^12 := by rw [mul_pow,←pow_mul]

#print axioms card_divisors_pow_le
#print axioms card_divisors_le_at_power_cutoff
end Erdos1206.DivisorPowerBound
