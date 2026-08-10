import FormalConjectures.Util.ProblemImports

open Nat

lemma two_pow_period (i : ℕ) : 2^(2 * 3^i) ≡ 1 [MOD 3^(i+1)] := by
  induction i with
  | zero =>
    rfl
  | succ i ih =>
    have h_rw : 2 * 3^(i+1) = (2 * 3^i) * 3 := by ring
    rw [h_rw, pow_mul]
    have h_mod : 2^(2 * 3^i) % 3^(i+1) = 1 := by
      have h_lt : 1 < 3^(i+1) := by
        have : 3^(i+1) ≥ 3 := @Nat.pow_le_pow_right 3 (by decide : 0 < 3) 1 (i+1) (by omega)
        omega
      have h1 : 1 % 3^(i+1) = 1 := Nat.mod_eq_of_lt h_lt
      rw [Nat.ModEq] at ih
      rw [h1] at ih
      exact ih
    have h_div := Nat.div_add_mod (2^(2 * 3^i)) (3^(i+1))
    have h_eq : 2^(2 * 3^i) = 3^(i+1) * (2^(2 * 3^i) / 3^(i+1)) + 1 := by omega
    rw [h_eq]
    -- Let q := 2^(2 * 3^i) / 3^(i+1)
    let q := 2^(2 * 3^i) / 3^(i+1)
    have h_poly : (3^(i+1) * q + 1)^3 = 3^(i+2) * (q * (3^i * q * (3^(i+1) * q) + 3^(i+1) * q + 1)) + 1 := by
      have h_pow1 : 3^(i+1) = 3 * 3^i := by
        rw [pow_succ]
        ring
      have h_pow2 : 3^(i+2) = 9 * 3^i := by
        have : i + 2 = i + 1 + 1 := by omega
        rw [this, pow_add]
        ring
      rw [h_pow1, h_pow2]
      generalize 3^i = Z
      ring
    rw [h_poly]
    -- now we have (3^(i+2) * Q + 1) % 3^(i+2) = 1
    have h_final : 3^(i+2) * (q * (3^i * q * (3^(i+1) * q) + 3^(i+1) * q + 1)) + 1 ≡ 1 [MOD 3^(i+2)] := by
      rw [Nat.ModEq]
      rw [add_comm]
      rw [Nat.add_mul_mod_self_left]
    exact h_final

lemma two_pow_mod_eq (k r i q : ℕ) (h_eq : k = r + q * (2 * 3^i)) : 2^k ≡ 2^r [MOD 3^(i+1)] := by
  rw [h_eq]
  rw [pow_add 2 r]
  have h_mul_comm : q * (2 * 3^i) = (2 * 3^i) * q := by ring
  rw [h_mul_comm]
  rw [pow_mul]
  have h_base := two_pow_period i
  have h_pow : (2^(2 * 3^i))^q ≡ 1^q [MOD 3^(i+1)] := Nat.ModEq.pow q h_base
  have h_one : 1^q = 1 := by simp
  rw [h_one] at h_pow
  have h_mul := Nat.ModEq.mul_left (2^r) h_pow
  rw [mul_one] at h_mul
  exact h_mul

lemma two_pow_sub_one_mod_eq (k r i q : ℕ) (h_eq : k = r + q * (2 * 3^i)) : (2^k - 1) % 3^(i+1) = (2^r - 1) % 3^(i+1) := by
  have h_mod := two_pow_mod_eq k r i q h_eq
  have h_div_k := Nat.div_add_mod (2^k) (3^(i+1))
  have h_div_r := Nat.div_add_mod (2^r) (3^(i+1))
  have h_not_dvd_k : 3^(i+1) ∣ 2^k → False := by
    intro hd
    have h_prime : Nat.Prime 3 := Nat.prime_three
    have h_dvd_pow : 3 ∣ 2^k := by
      have h_dvd_three : 3 ∣ 3^(i+1) := by
        use 3^i
        ring
      exact Nat.dvd_trans h_dvd_three hd
    have h_dvd_two : 3 ∣ 2 := h_prime.dvd_of_dvd_pow h_dvd_pow
    contradiction
  have h_not_dvd_r : 3^(i+1) ∣ 2^r → False := by
    intro hd
    have h_prime : Nat.Prime 3 := Nat.prime_three
    have h_dvd_three : 3 ∣ 3^(i+1) := by
      use 3^i
      ring
    have h_dvd_2r : 3 ∣ 2^r := Nat.dvd_trans h_dvd_three hd
    have h_dvd_2 : 3 ∣ 2 := h_prime.dvd_of_dvd_pow h_dvd_2r
    contradiction
  have h_rem_nz_k : 2^k % 3^(i+1) ≠ 0 := by
    intro hc
    have := Nat.dvd_of_mod_eq_zero hc
    exact h_not_dvd_k this
  have h_rem_nz_r : 2^r % 3^(i+1) ≠ 0 := by
    intro hc
    have : 3^(i+1) ∣ 2^r := Nat.dvd_of_mod_eq_zero hc
    exact h_not_dvd_r this
  have h_eq_mul_k : 2^k = (2^k / 3^(i+1)) * 3^(i+1) + 2^k % 3^(i+1) := by
    have h_comm : 3^(i+1) * (2^k / 3^(i+1)) = (2^k / 3^(i+1)) * 3^(i+1) := by ring
    rw [h_comm] at h_div_k
    exact h_div_k.symm
  have h_eq_mul_r : 2^r = (2^r / 3^(i+1)) * 3^(i+1) + 2^r % 3^(i+1) := by
    have h_comm : 3^(i+1) * (2^r / 3^(i+1)) = (2^r / 3^(i+1)) * 3^(i+1) := by ring
    rw [h_comm] at h_div_r
    exact h_div_r.symm
  have h_rem_ge_k : 2^k % 3^(i+1) ≥ 1 := Nat.pos_of_ne_zero h_rem_nz_k
  have h_rem_ge_r : 2^r % 3^(i+1) ≥ 1 := Nat.pos_of_ne_zero h_rem_nz_r
  have h_rw_k : 2^k - 1 = (2^k / 3^(i+1)) * 3^(i+1) + (2^k % 3^(i+1) - 1) := by omega
  have h_rw_r : 2^r - 1 = (2^r / 3^(i+1)) * 3^(i+1) + (2^r % 3^(i+1) - 1) := by omega
  rw [h_rw_k, h_rw_r]
  rw [add_comm (2^k / 3^(i+1) * 3^(i+1))]
  rw [add_comm (2^r / 3^(i+1) * 3^(i+1))]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
  have h_lt_k : 2^k % 3^(i+1) - 1 < 3^(i+1) := by
    have : 2^k % 3^(i+1) < 3^(i+1) := Nat.mod_lt _ (by positivity)
    omega
  have h_lt_r : 2^r % 3^(i+1) - 1 < 3^(i+1) := by
    have : 2^r % 3^(i+1) < 3^(i+1) := Nat.mod_lt _ (by positivity)
    omega
  rw [Nat.mod_eq_of_lt h_lt_k, Nat.mod_eq_of_lt h_lt_r]
  rw [Nat.ModEq] at h_mod
  rw [h_mod]

lemma mod_mul_div_self_eq (a b c : ℕ) (hb : b > 0) : a % (b * c) / b = (a / b) % c := by
  by_cases hc : c = 0
  · rw [hc]
    simp
  · have hc_pos : c > 0 := Nat.pos_of_ne_zero hc
    have h_mul_pos : b * c > 0 := Nat.mul_pos hb hc_pos
    have h_div_add_mod : a = (b * c) * (a / (b * c)) + a % (b * c) := (Nat.div_add_mod a (b * c)).symm
    have h_rem_lt : a % (b * c) < b * c := Nat.mod_lt a h_mul_pos
    have h_rw : a / b = ((a % (b * c)) + b * (c * (a / (b * c)))) / b := by
      nth_rewrite 1 [h_div_add_mod]
      congr 1
      ring
    rw [h_rw]
    rw [Nat.add_mul_div_left (a % (b * c)) (c * (a / (b * c))) hb]
    rw [Nat.add_mul_mod_self_left]
    have h_lt : a % (b * c) / b < c := by
      exact Nat.div_lt_of_lt_mul h_rem_lt
    exact (Nat.mod_eq_of_lt h_lt).symm

lemma digit_periodic (k r i q : ℕ) (h_eq : k = r + q * (2 * 3^i)) : (2^k - 1) / 3^i % 3 = (2^r - 1) / 3^i % 3 := by
  have h_mod := two_pow_sub_one_mod_eq k r i q h_eq
  have h_digit (X : ℕ) : X / 3^i % 3 = (X % 3^(i+1)) / 3^i := by
    have h_pow : 3^(i+1) = 3^i * 3 := by
      rw [pow_succ]
    have h_pow_pos : 3^i > 0 := Nat.pos_of_ne_zero (pow_ne_zero i (by omega))
    rw [h_pow]
    rw [mod_mul_div_self_eq X (3^i) 3 h_pow_pos]
  rw [h_digit (2^k - 1), h_digit (2^r - 1)]
  rw [h_mod]

