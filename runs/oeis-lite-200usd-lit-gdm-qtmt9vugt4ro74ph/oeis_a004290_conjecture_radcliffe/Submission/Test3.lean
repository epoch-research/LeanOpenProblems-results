import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A004290 (n : ℕ) : ℕ :=
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  sInf S

theorem test_large (n : ℕ) (hn : n < 1000) (hn17 : n ≥ 17) : A004290 n < (10^18 - 1) / 9 := sorry

theorem A004290_lt_geom_sum (n : ℕ) (hn : n > 0) : A004290 n < (10^(n + 1) - 1) / 9 := sorry

lemma A004290_le_ten_pow_mul (n k : ℕ) (d : ℕ) (hd : d ∣ 10^k) (hu : d ∣ n) (hn : n > 0) :
    A004290 n ≤ 10^k * A004290 (n / d) := sorry

theorem dvd_pow_ten_sub_one (n : ℕ) : 9 ∣ 10^n - 1 := sorry

theorem main_goal (k : ℕ) (hk : k ≥ 4) (n : ℕ) (hn_pos : n > 0) (hn : n < 10 ^ k - 1)
    (u3 : ℕ) (hu3_pos : u3 > 0) (d3 : ℕ) (hd3 : d3 ∣ 10^(k-3)) (hu3 : d3 ∣ n) (hu3_eq : u3 = n / d3)
    (hu3_ge : u3 + 1 ≥ 8 * k + 1) :
    A004290 n < (10 ^ (9 * k) - 1) / 9 := by
  by_cases hu3_lt_1000 : u3 < 1000
  · have hn_ge_17 : u3 ≥ 17 := by omega
    have h_lt_18 := test_large u3 hu3_lt_1000 hn_ge_17
    have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := by
      rw [hu3_eq]
      exact A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
    have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
      have h_eqA : 9 * ((10^18 - 1) / 9) = 10^18 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 18)
      have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
      have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
        rw [h_eqB]
        calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
          _ < 10^(k-3) * (10^18 - 1) := by
            apply Nat.mul_lt_mul_of_pos_left
            · have : 9 * A004290 u3 < 9 * ((10^18 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_18 (by norm_num)
              rw [h_eqA] at this
              exact this
            · exact Nat.pow_pos (by norm_num)
          _ = 10^(k+15) - 10^(k-3) := by
            rw [Nat.mul_sub_left_distrib, mul_one]
            have h_pow : 10^(k-3) * 10^18 = 10^(k+15) := by
              rw [← pow_add]
              congr 1
              omega
            rw [h_pow]
          _ < 10^(9 * k) - 1 := by
            have h_pow_lt : 10^(k+15) < 10^(9 * k) := by
              exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
            have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
            have h_pow_le : 10^(k-3) ≤ 10^(k+15) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
      exact Nat.lt_of_mul_lt_mul_left h_mul_lt
    exact lt_of_le_of_lt h_le_M3 h_lt_M3
  · sorry
