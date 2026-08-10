import FormalConjectures.Util.ProblemImports

open Nat Set

lemma even_three_prime_case {n : ℕ} {k j a : ℕ} {q : ℕ} (hq : Nat.Prime q) (hk : k ≥ 1) (hj : j ≥ 1) (ha : a ≥ 1) (hn : n + 1 = 2^k * 3^j * q^a) (hq_ge : q ≥ 5) :
  ∃ x, x > 0 ∧ (x - 1) % Nat.totient x = n := by
  use 2^k * 3^j * q^(a+1)
  have h_x_pos : 2^k * 3^j * q^(a+1) > 0 := by positivity
  refine ⟨h_x_pos, ?_⟩
  have h_cop23 : Nat.Coprime 2 3 := by decide
  have h_cop2q : Nat.Coprime 2 q := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    have h_le : q ≤ 2 := Nat.le_of_dvd (by decide : 2 > 0) hdvd
    omega
  have h_cop3q : Nat.Coprime 3 q := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    have h_le : q ≤ 3 := Nat.le_of_dvd (by decide : 3 > 0) hdvd
    omega
  have h_coprime1 : Nat.Coprime (2^k) (3^j) := Nat.Coprime.pow k j h_cop23
  have h_coprime2 : Nat.Coprime (2^k * 3^j) (q^(a+1)) := by
    apply Nat.Coprime.mul_left
    · exact Nat.Coprime.pow k (a+1) h_cop2q
    · exact Nat.Coprime.pow j (a+1) h_cop3q
  have h_tot : (2^k * 3^j * q^(a+1)).totient = 2^k * 3^(j-1) * q^a * (q - 1) := by
    rw [Nat.totient_mul h_coprime2]
    rw [Nat.totient_mul h_coprime1]
    have h_tot2 : (2^k).totient = 2^(k-1) := by
      have h2_pow := Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k)
      rw [h2_pow]
      ring
    have h_tot3 : (3^j).totient = 3^(j-1) * 2 := by
      have h3_pow := Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < j)
      rw [h3_pow]
    have h_totq : (q^(a+1)).totient = q^a * (q - 1) := by
      have hq_pow := Nat.totient_prime_pow hq (by omega : 0 < a + 1)
      have h_sub : a + 1 - 1 = a := by omega
      rw [hq_pow, h_sub]
    rw [h_tot2, h_tot3, h_totq]
    have h2_pow_succ : 2^k = 2^(k-1) * 2 := by
      have : k = k - 1 + 1 := by omega
      conv_lhs => rw [this]
      rw [pow_succ]
    rw [h2_pow_succ]
    ring
  rw [h_tot]
  have h_cancel : 2^k * 3^j * q^(a+1) = (2^k * 3^(j-1) * q^a * (q - 1)) * 3 + 2^k * 3^j * q^a := by
    have h1 : (2^k * 3^(j-1) * q^a * (q - 1)) * 3 = 2^k * 3^j * q^a * (q - 1) := by
      calc (2^k * 3^(j-1) * q^a * (q - 1)) * 3
        _ = 2^k * (3^(j-1) * 3) * q^a * (q - 1) := by ring
        _ = 2^k * 3^j * q^a * (q - 1) := by
          have h3_pow_succ : 3^j = 3^(j-1) * 3 := by
            have : j = j - 1 + 1 := by omega
            conv_lhs => rw [this]
            rw [pow_succ]
          rw [h3_pow_succ]
    rw [h1]
    have h2 : 2^k * 3^j * q^a * (q - 1) = 2^k * 3^j * q^(a+1) - 2^k * 3^j * q^a := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have h_pow : 2^k * 3^j * q^a * q = 2^k * 3^j * q^(a+1) := by
        calc 2^k * 3^j * q^a * q
          _ = 2^k * 3^j * (q^a * q) := by ring
          _ = 2^k * 3^j * q^(a+1) := by rw [← pow_succ]
      rw [h_pow]
    rw [h2]
    have h_le : 2^k * 3^j * q^a ≤ 2^k * 3^j * q^(a+1) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by omega : q ≥ 1) (by omega : a ≤ a + 1)
    rw [Nat.sub_add_cancel h_le]
  have h_eq : 2^k * 3^j * q^(a+1) - 1 = (2^k * 3^(j-1) * q^a * (q - 1)) * 3 + n := by
    omega
  rw [h_eq]
  have h_mod_self : ((2^k * 3^(j-1) * q^a * (q - 1)) * 3 + n) % (2^k * 3^(j-1) * q^a * (q - 1)) = n % (2^k * 3^(j-1) * q^a * (q - 1)) := by
    have h_rw : (2^k * 3^(j-1) * q^a * (q - 1)) * 3 + n = n + (2^k * 3^(j-1) * q^a * (q - 1)) * 3 := by ring
    rw [h_rw]
    exact Nat.add_mul_mod_self_left n (2^k * 3^(j-1) * q^a * (q - 1)) 3
  rw [h_mod_self]
  have h_lt : n < 2^k * 3^(j-1) * q^a * (q - 1) := by
    have h_n_lt : n < n + 1 := by omega
    rw [hn] at h_n_lt
    have h3_pow_succ : 3^j = 3^(j-1) * 3 := by
      have : j = j - 1 + 1 := by omega
      conv_lhs => rw [this]
      rw [pow_succ]
    rw [h3_pow_succ] at h_n_lt
    have h_ge : 2^k * (3^(j-1) * 3) * q^a ≤ 2^k * 3^(j-1) * q^a * (q - 1) := by
      have h_q_sub : 3 ≤ q - 1 := by omega
      have h_mul := Nat.mul_le_mul_left (2^k * 3^(j-1) * q^a) h_q_sub
      have h_rw1 : 2^k * (3^(j-1) * 3) * q^a = 2^k * 3^(j-1) * q^a * 3 := by ring
      have h_rw2 : 2^k * 3^(j-1) * q^a * (q - 1) = 2^k * 3^(j-1) * q^a * (q - 1) := by ring
      rw [h_rw1]
      exact h_mul
    omega
  rw [Nat.mod_eq_of_lt h_lt]
