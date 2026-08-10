import Mathlib

open Nat Set

theorem coprime_pow_ge5_three (p k b : ℕ) (hp : Nat.Prime p) (hp_ge5 : p ≥ 5) :
    Coprime (p^(k+1)) (3^b) := by
  have h_coprime : Coprime p 3 := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have hp_le : p ≤ 3 := Nat.le_of_dvd (by decide) hdvd
    omega
  exact Coprime.pow (k+1) b h_coprime

theorem coprime_pow_ge5_two (p k a : ℕ) (hp : Nat.Prime p) (hp_ge5 : p ≥ 5) :
    Coprime (p^(k+1)) (2^a) := by
  have h_coprime : Coprime p 2 := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  exact Coprime.pow (k+1) a h_coprime

theorem coprime_three_two (b a : ℕ) : Coprime (3^b) (2^a) := by
  have h : Coprime 3 2 := by decide
  exact Coprime.pow b a h

theorem totient_x_eq_3 (p k a b : ℕ) (hp : Nat.Prime p) (hp_ge5 : p ≥ 5) (ha : a ≥ 1) (hb : b ≥ 1) :
    Nat.totient (p^(k+1) * 2^a * 3^b) = p^k * (p - 1) * 2^(a-1) * 2 * 3^(b-1) := by
  have h_assoc : p^(k+1) * 2^a * 3^b = p^(k+1) * (2^a * 3^b) := by ring
  rw [h_assoc]
  have h_coprime1 : Coprime (p^(k+1)) (2^a * 3^b) := by
    have h1 := coprime_pow_ge5_two p k a hp hp_ge5
    have h2 := coprime_pow_ge5_three p k b hp hp_ge5
    exact Coprime.mul_right h1 h2
  rw [Nat.totient_mul h_coprime1]
  have h_tot_23 : Nat.totient (2^a * 3^b) = Nat.totient (2^a) * Nat.totient (3^b) := by
    have h_comm : 2^a * 3^b = 3^b * 2^a := mul_comm _ _
    rw [h_comm]
    have h_coprime3 := coprime_three_two b a
    rw [Nat.totient_mul h_coprime3]
    ring
  rw [h_tot_23]
  have h_prime_pow : Nat.totient (p^(k+1)) = p^k * (p - 1) := by
    have h_pos : 0 < k + 1 := by omega
    have h_tot := Nat.totient_prime_pow hp h_pos
    rw [h_tot]
    have h_sub : k + 1 - 1 = k := by omega
    rw [h_sub]
  have h_tot2 : Nat.totient (2^a) = 2^(a-1) := by
    have h_prime2 : Nat.Prime 2 := Nat.prime_two
    have h_tot2_eq := Nat.totient_prime_pow h_prime2 ha
    rw [h_tot2_eq]
    have : 2 - 1 = 1 := by decide
    rw [this, mul_one]
  have h_tot3 : Nat.totient (3^b) = 2 * 3^(b-1) := by
    have h_prime3 : Nat.Prime 3 := Nat.prime_three
    have h_tot3_eq := Nat.totient_prime_pow h_prime3 hb
    rw [h_tot3_eq]
    have : 3 - 1 = 2 := by decide
    rw [this]
    ring
  rw [h_prime_pow, h_tot2, h_tot3]
  ring

theorem solve_p_pow_k_mul_pow_2_mul_pow_3 (p k a b : ℕ) (hp : Nat.Prime p) (hp_ge5 : p ≥ 5) (hk : k ≥ 1) (ha : a ≥ 1) (hb : b ≥ 1) :
    let n := p^k * 2^a * 3^b - 1
    let x := p^(k+1) * 2^a * 3^b
    x > 0 ∧ (x - 1) % Nat.totient x = n := by
  have h_x_pos : p^(k+1) * 2^a * 3^b > 0 := by
    have h1 : p^(k+1) > 0 := pos_of_gt (by positivity)
    have h2 : 2^a > 0 := pos_of_gt (by positivity)
    have h3 : 3^b > 0 := pos_of_gt (by positivity)
    exact Nat.mul_pos (Nat.mul_pos h1 h2) h3
  refine ⟨h_x_pos, ?_⟩
  have h_tot := totient_x_eq_3 p k a b hp hp_ge5 ha hb
  have h_tot_simpl : Nat.totient (p^(k+1) * 2^a * 3^b) = p^k * (p - 1) * 2^(a-1) * 3^(b-1) * 2 := by
    rw [h_tot]
    ring
  rw [h_tot_simpl]
  have h_pow1 : p^(k+1) = p^k * p := by ring
  have h_pow2 : 2^a = 2^(a-1) * 2 := by
    have : a = a - 1 + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_add, pow_one]
  have h_pow3 : 3^b = 3^(b-1) * 3 := by
    have : b = b - 1 + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_add, pow_one]
  rw [h_pow1, h_pow2, h_pow3]
  generalize hpk : p^k = P1
  generalize h2a : 2^(a-1) = P2
  generalize h3b : 3^(b-1) = P3
  generalize h_A : P1 * P2 * P3 = A
  generalize h_B : P1 * p * P2 * P3 = B
  have h_a_pos : 0 < A := by
    rw [← h_A]
    have h_p1 : 0 < P1 := by rw [← hpk]; positivity
    have h_p2 : 0 < P2 := by rw [← h2a]; positivity
    have h_p3 : 0 < P3 := by rw [← h3b]; positivity
    exact Nat.mul_pos (Nat.mul_pos h_p1 h_p2) h_p3
  have h_flat1 : P1 * p * (P2 * 2) * (P3 * 3) = B * 6 := by
    rw [← h_B]
    ring
  have h_flat2 : P1 * (P2 * 2) * (P3 * 3) = A * 6 := by
    rw [← h_A]
    ring
  have h_ab_ge : A * 5 ≤ B := by
    rw [← h_A, ← h_B]
    have h_le_p : P1 * P2 * P3 * 5 ≤ P1 * P2 * P3 * p := Nat.mul_le_mul_left _ hp_ge5
    have h_eq : P1 * P2 * P3 * p = P1 * p * P2 * P3 := by ring
    rw [h_eq] at h_le_p
    exact h_le_p
  have h_div : B * 6 - 1 = (A * 6 - 1) + P1 * (p - 1) * P2 * P3 * 2 * 3 := by
    have h_ge : A * 6 ≤ B * 6 := by omega
    have h_mul : P1 * (p - 1) * P2 * P3 * 2 * 3 = B * 6 - A * 6 := by
      have h1 : P1 * (p - 1) = P1 * p - P1 := by
        rw [Nat.mul_sub_left_distrib]
        simp
      have h_assoc1 : P1 * (p - 1) * P2 * P3 * 2 * 3 = (P1 * (p - 1) * P2 * P3) * 6 := by ring
      rw [h_assoc1, h1]
      rw [Nat.sub_mul, Nat.sub_mul, Nat.sub_mul]
      rw [h_A, h_B]
    rw [h_mul]
    omega
  rw [h_flat1, h_flat2, h_div]
  have h_lt : A * 6 - 1 < P1 * (p - 1) * P2 * P3 * 2 := by
    have h_mul : P1 * (p - 1) * P2 * P3 * 2 = B * 2 - A * 2 := by
      have h1 : P1 * (p - 1) = P1 * p - P1 := by
        rw [Nat.mul_sub_left_distrib]
        simp
      have h_assoc1 : P1 * (p - 1) * P2 * P3 * 2 = (P1 * (p - 1) * P2 * P3) * 2 := by ring
      rw [h_assoc1, h1]
      rw [Nat.sub_mul, Nat.sub_mul, Nat.sub_mul]
      rw [h_A, h_B]
    rw [h_mul]
    omega
  rw [Nat.add_mul_mod_self_left (A * 6 - 1) (P1 * (p - 1) * P2 * P3 * 2) 3, Nat.mod_eq_of_lt h_lt]
