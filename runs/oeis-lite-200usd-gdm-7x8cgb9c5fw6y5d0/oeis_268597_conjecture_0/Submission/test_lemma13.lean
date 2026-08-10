import FormalConjectures.Util.ProblemImports

open Nat Set

lemma even_two_prime_case {n : ℕ} {k a : ℕ} {q : ℕ} (hq : Nat.Prime q) (hk : k ≥ 1) (ha : a ≥ 1) (hn : n + 1 = 2^k * q^a) (hq_ge : q ≥ 3) :
  ∃ x, x > 0 ∧ (x - 1) % Nat.totient x = n := by
  use 2^k * q^(a+1)
  have h_x_pos : 2^k * q^(a+1) > 0 := by positivity
  refine ⟨h_x_pos, ?_⟩
  have h_cop2q : Nat.Coprime 2 q := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    have h_le : q ≤ 2 := Nat.le_of_dvd (by decide : 2 > 0) hdvd
    omega
  have h_coprime2 : Nat.Coprime (2^k) (q^(a+1)) := Nat.Coprime.pow k (a+1) h_cop2q
  have h_tot : (2^k * q^(a+1)).totient = 2^(k-1) * q^a * (q - 1) := by
    rw [Nat.totient_mul h_coprime2]
    have h_tot2 : (2^k).totient = 2^(k-1) := by
      have h2_pow := Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k)
      rw [h2_pow]
      ring
    have h_totq : (q^(a+1)).totient = q^a * (q - 1) := by
      have hq_pow := Nat.totient_prime_pow hq (by omega : 0 < a + 1)
      have h_sub : a + 1 - 1 = a := by omega
      rw [hq_pow, h_sub]
    rw [h_tot2, h_totq]
    ring
  rw [h_tot]
  have h_cancel : 2^k * q^(a+1) = (2^(k-1) * q^a * (q - 1)) * 2 + 2^k * q^a := by
    have h1 : (2^(k-1) * q^a * (q - 1)) * 2 = 2^k * q^a * (q - 1) := by
      have h2_pow_succ : 2^k = 2^(k-1) * 2 := by
        have : k = k - 1 + 1 := by omega
        conv_lhs => rw [this]
        rw [pow_succ]
      rw [h2_pow_succ]
      ring
    rw [h1]
    have h2 : 2^k * q^a * (q - 1) = 2^k * q^(a+1) - 2^k * q^a := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have h_pow : 2^k * q^a * q = 2^k * q^(a+1) := by
        calc 2^k * q^a * q
          _ = 2^k * (q^a * q) := by ring
          _ = 2^k * q^(a+1) := by rw [← pow_succ]
      rw [h_pow]
    rw [h2]
    have h_le : 2^k * q^a ≤ 2^k * q^(a+1) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by omega : q ≥ 1) (by omega : a ≤ a + 1)
    rw [Nat.sub_add_cancel h_le]
  have h_eq : 2^k * q^(a+1) - 1 = (2^(k-1) * q^a * (q - 1)) * 2 + n := by
    omega
  rw [h_eq]
  have h_mod_self : ((2^(k-1) * q^a * (q - 1)) * 2 + n) % (2^(k-1) * q^a * (q - 1)) = n % (2^(k-1) * q^a * (q - 1)) := by
    have h_rw : (2^(k-1) * q^a * (q - 1)) * 2 + n = n + (2^(k-1) * q^a * (q - 1)) * 2 := by ring
    rw [h_rw]
    exact Nat.add_mul_mod_self_left n (2^(k-1) * q^a * (q - 1)) 2
  rw [h_mod_self]
  have h_lt : n < 2^(k-1) * q^a * (q - 1) := by
    have h_n_lt : n < n + 1 := by omega
    rw [hn] at h_n_lt
    have h2_pow_succ : 2^k = 2^(k-1) * 2 := by
      have : k = k - 1 + 1 := by omega
      conv_lhs => rw [this]
      rw [pow_succ]
    rw [h2_pow_succ] at h_n_lt
    have h_ge : 2^(k-1) * 2 * q^a ≤ 2^(k-1) * q^a * (q - 1) := by
      have h_q_sub : 2 ≤ q - 1 := by omega
      have h_mul := Nat.mul_le_mul_left (2^(k-1) * q^a) h_q_sub
      have h_rw1 : 2^(k-1) * 2 * q^a = 2^(k-1) * q^a * 2 := by ring
      have h_rw2 : 2^(k-1) * q^a * (q - 1) = 2^(k-1) * q^a * (q - 1) := by ring
      rw [h_rw1]
      exact h_mul
    omega
  rw [Nat.mod_eq_of_lt h_lt]
