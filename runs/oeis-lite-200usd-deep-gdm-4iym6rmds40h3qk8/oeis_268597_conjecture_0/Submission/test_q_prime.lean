import Mathlib

open Nat

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

theorem solve_q_prime (n : ℕ) (q : ℕ) (p : ℕ) (hq : q.Prime) (hp : p.Prime) (hq_ge3 : q ≥ 3) (hp_gt_q : p > q)
    (hn : n - (q - 2) = p) (hn_ge : n ≥ q - 2) :
    q * p ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := by
  simp only [Set.mem_setOf_eq]
  have h_x_pos : q * p > 0 := Nat.mul_pos hq.pos hp.pos
  refine ⟨h_x_pos, ?_⟩
  have h_coprime : Coprime q p := by
    rw [hq.coprime_iff_not_dvd]
    intro hdvd
    have h_eq : q = p := (hp.eq_one_or_self_of_dvd q hdvd).resolve_left hq.ne_one
    omega
  have h_tot : Nat.totient (q * p) = (q - 1) * (p - 1) := by
    rw [Nat.totient_mul h_coprime, Nat.totient_prime hq, Nat.totient_prime hp]
  rw [h_tot]
  have h_eq : q * p - 1 = n + (q - 1) * (p - 1) * 1 := by
    have h_n : n = p + q - 2 := by omega
    rw [h_n]
    simp only [mul_one]
    have hq_pos : q ≥ 1 := by omega
    have hp_pos : p ≥ 1 := by omega
    -- Let's prove: q * p - 1 = (p + q - 2) + (q - 1) * (p - 1)
    -- We can expand (q - 1) * (p - 1) = q * p - q - p + 1
    have h_mul : (q - 1) * (p - 1) = q * p - q - p + 1 := by
      have h_dist1 : (q - 1) * (p - 1) = (q - 1) * p - (q - 1) * 1 := Nat.mul_sub_left_distrib (q - 1) p 1
      simp only [mul_one] at h_dist1
      have h_dist2 : (q - 1) * p = q * p - 1 * p := Nat.sub_mul q 1 p
      simp only [one_mul] at h_dist2
      have h_dist3 : (q - 1) = q - 1 := rfl
      omega
    omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_left]
  have h_lt : n < (q - 1) * (p - 1) := by
    have h_n : n = p + q - 2 := by omega
    rw [h_n]
    have hp_odd : p ≠ 2 := by omega
    have hq_odd : q ≠ 2 := by
      intro h_eq2
      subst h_eq2
      omega
    have hpq : p ≠ q := by omega
    have h_ineq := prime_ineq p q hp hp_odd hq hq_odd hpq.symm
    omega
  exact Nat.mod_eq_of_lt h_lt
