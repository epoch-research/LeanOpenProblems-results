import Mathlib

open Nat Set

theorem coprime_pow_primes (p q k : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Coprime (p^(k+1)) q := by
  have h_coprime : Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have hp_eq : p = q := by
      rcases hq.eq_one_or_self_of_dvd p hdvd with h1 | h2
      · exfalso
        exact hp.ne_one h1
      · exact h2
    exact hpq hp_eq
  exact Coprime.pow_left (k+1) h_coprime

theorem totient_p_pow_k_mul_q (p q k : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Nat.totient (p^(k+1) * q) = p^k * (p - 1) * (q - 1) := by
  have h_coprime := coprime_pow_primes p q k hp hq hpq
  rw [Nat.totient_mul h_coprime]
  have h_prime_pow : Nat.totient (p^(k+1)) = p^k * (p - 1) := by
    have h_pos : 0 < k + 1 := by omega
    have h_tot := Nat.totient_prime_pow hp h_pos
    rw [h_tot]
    have h_sub : k + 1 - 1 = k := by omega
    rw [h_sub]
  rw [h_prime_pow, Nat.totient_prime hq]


theorem prime_odd (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : Odd p := by
  rcases hp.eq_two_or_odd with h2 | h_odd
  · contradiction
  · rwa [Nat.odd_iff]

theorem odd_ge_3 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : p ≥ 3 := by
  have h_odd := prime_odd p hp hp2
  have h2 := hp.two_le
  omega

theorem prime_ineq (p q : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hq : Nat.Prime q) (hq_odd : q ≠ 2) (hpq : p ≠ q) :
    p + q - 1 ≤ (p - 1) * (q - 1) := by
  have hp3 := odd_ge_3 p hp hp_odd
  have hq3 := odd_ge_3 q hq hq_odd
  rcases lt_trichotomy p q with hlt | rfl | hgt
  · -- p < q
    have h1 : p + q - 1 ≤ 2 * q - 2 := by omega
    have h2 : 2 * q - 2 ≤ (p - 1) * (q - 1) := by
      have : p - 1 ≥ 2 := by omega
      have hp_ge : 2 ≤ p - 1 := by omega
      have : 2 * (q - 1) ≤ (p - 1) * (q - 1) := Nat.mul_le_mul_right (q - 1) hp_ge
      omega
    exact le_trans h1 h2
  · contradiction
  · -- q < p
    have h1 : p + q - 1 ≤ 2 * p - 2 := by omega
    have h2 : 2 * p - 2 ≤ (p - 1) * (q - 1) := by
      have : q - 1 ≥ 2 := by omega
      have hq_ge : 2 ≤ q - 1 := by omega
      have : (p - 1) * 2 ≤ (p - 1) * (q - 1) := Nat.mul_le_mul_left (p - 1) hq_ge
      omega
    exact le_trans h1 h2

