import Submission.Spec

open Nat Finset ArithmeticFunction

theorem test_hb_odd (n : ℕ) (p : ℕ) (hp : p ∈ n.primeFactorsList) (hp_odd : p % 2 = 1)
  (hn_nz : n ≠ 0) (b : ℕ) (m : ℕ) (h_eq_mul : n = 2^b * m) (hm_nz : m ≠ 0)
  (h_cop' : Nat.Coprime (2^b) m) (hm_odd : m % 2 = 1) (hp_dvd_m : p ∣ m) (hm_gt1 : 1 < m)
  (q1 q2 : ℚ) (hq1_pos : q1.num > 0) (hq2_pos : q2.num > 0)
  (hq1_def : q1 = ((2^b).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)))
  (hq2_def : q2 = (m.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)))
  (hn_eq_sum : (n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)) = q1 * q2)
  (h_den : ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1)
  (hb_odd : b % 2 = 1) : False := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  let k := b / 2
  have h_eq_2k1 : b = 2 * k + 1 := by omega
  have h_q1_even : q1 = (((2^(2*k+1)).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) := by
    rw [hq1_def, h_eq_2k1]
  have h_q1_val : 1 ≤ padicValRat 2 q1 := by
    rw [h_q1_even]
    exact padicValRat_two_sum_divisors_pow_two_odd k
  have h_q2_val_le : padicValRat 2 q2 ≤ - (padicValNat 2 (p + 1) : ℤ) := by
    rw [hq2_def]
    exact padicValRat_two_sum_divisors_odd_le m p hp_prime hp_odd hp_dvd_m hm_odd hm_gt1
  have h_den_q : (q1 * q2).den = 1 := by
    rw [← hn_eq_sum]
    exact h_den
  have h_cop : Nat.Coprime q1.den q2.den := coprime_den q1 q2 hq1_pos h_den_q
  have h_q2_den_even : 2 ∣ q2.den := by
    apply even_den_of_padicValRat_neg 2 q2
    have hp_nz : p + 1 ≠ 0 := by omega
    have h_dvd : 2 ∣ p + 1 := by
      have : (p + 1) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have hV_pos : 1 ≤ padicValNat 2 (p + 1) := one_le_padicValNat_of_dvd hp_nz h_dvd
    have : padicValRat 2 q2 < 0 := by omega
    exact this
  have h_q1_den_odd : q1.den % 2 = 1 := by
    have hval_nonneg : 0 ≤ padicValRat 2 q1 := by omega
    have hval_zero := den_odd_of_val_nonneg q1 hval_nonneg
    have h_dvd_iff : ¬ 2 ∣ q1.den := by
      intro h_dvd
      have : 1 ≤ padicValNat 2 q1.den := one_le_padicValNat_of_dvd (by positivity) h_dvd
      omega
    omega
  sorry
